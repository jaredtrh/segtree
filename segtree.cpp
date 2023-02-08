#include <bits/stdc++.h>
using namespace std;

//#define GOOGLE
//#define TEST_CASES

template<typename T, T Id>
class segtreebase {
protected:
    size_t size_;
    vector<T> tree_;
    static size_t firstexp2(size_t n) {
        size_t exp2 = 1;
        while (exp2 < n) exp2 <<= 1;
        return exp2;
    }
    static inline size_t leftidx(size_t i) { return i * 2 + 1; }
    static inline size_t rightidx(size_t i) { return i * 2 + 2; }
    static inline size_t parentidx(size_t i) { return (i - 1) / 2; }
    inline size_t leafidx(size_t i) const { return tree_.size() - size_ + i; }
    static inline size_t mid(size_t l, size_t r) { return l + (r - l) / 2; }
    struct segnode { size_t i, l, r; };
public:
    explicit segtreebase(size_t n) : size_(firstexp2(n)), tree_(size_ * 2 - 1, Id) {}
    segtreebase(size_t n, const T& init) : size_(firstexp2(n)) {
        tree_.reserve(size_ * 2 - 1);
        fill_n(back_inserter(tree_), size_ - 1, Id);
        fill_n(back_inserter(tree_), n, init);
        fill_n(back_inserter(tree_), tree_.capacity() - tree_.size(), Id);
    }
    template<typename InputIt, typename iterator_traits<InputIt>::value_type* = nullptr>
    segtreebase(InputIt first, InputIt last) : size_(firstexp2(distance(first, last))) {
        tree_.reserve(size_ * 2 - 1);
        fill_n(back_inserter(tree_), size_ - 1, Id);
        tree_.insert(tree_.end(), first, last);
        fill_n(back_inserter(tree_), tree_.capacity() - tree_.size(), Id);
    }
    size_t size() const { return size_; }
    const T& operator[](size_t i) const { return tree_[leafidx(i)]; }
};

template<typename T = int, T Id = 0, typename F = plus<T>>
class segtree : public segtreebase<T, Id> {
    using base = segtreebase<T, Id>;
private:
    using base::size_;
    using base::tree_;
    using base::leftidx;
    using base::rightidx;
    using base::parentidx;
    using base::leafidx;
    using base::mid;
    using typename base::segnode;
    F f_;
    template<typename T1 = T>
    inline auto f(const T1& lhs, const T& rhs, size_t, size_t, size_t) const -> decltype(f_(lhs, rhs)) {
        return f_(lhs, rhs);
    }
    template<typename T1 = T>
    inline auto f(const T1& lhs, const T& rhs, size_t l, size_t m, size_t r) const -> decltype(f_(lhs, rhs, l, m, r)) {
        return f_(lhs, rhs, l, m, r);
    }
    void build() {
        size_t l = 0;
        size_t r = 1;
        for (size_t i = tree_.size() - size_ - 1; i != static_cast<size_t>(-1); --i) {
            size_t len = r - l;
            if (l == 0) {
                l = size_ - len * 2;
                r = size_;
            } else {
                l -= len;
                r -= len;
            }
            tree_[i] = f(tree_[leftidx(i)], tree_[rightidx(i)], l, mid(l, r), r);
        }
    }
    template<typename U, typename Compare>
    size_t findpref(const U& x, Compare cmp, segnode node, T pref, size_t l) const {
        while (node.r - node.l > 1) {
            size_t left = leftidx(node.i);
            size_t m = mid(node.l, node.r);
            if (cmp(x, f(pref, tree_[left], l, node.l, m))) {
                node.i = left;
                node.r = m;
            } else {
                pref = f(pref, tree_[left], l, node.l, m);
                node.i = rightidx(node.i);
                node.l = m;
            }
        }
        return node.r;
    }
    template<typename U, typename Compare>
    size_t findsuf(const U& x, Compare cmp, segnode node, T suf, size_t r) const {
        while (node.r - node.l > 1) {
            size_t right = rightidx(node.i);
            size_t m = mid(node.l, node.r);
            if (cmp(x, f(tree_[right], suf, m, node.r, r))) {
                node.i = right;
                node.l = m;
            } else {
                suf = f(tree_[right], suf, m, node.r, r);
                node.i = leftidx(node.i);
                node.r = m;
            }
        }
        return node.l;
    }
public:
    template<typename F1 = F, enable_if_t<is_same_v<remove_reference_t<F1>, F>>* = nullptr>
    explicit segtree(size_t n, F1&& f = F1()) : base(n), f_(forward<F1>(f)) {}
    template<typename F1 = F>
    segtree(size_t n, const T& init, F1&& f = F1()) : base(n, init), f_(forward<F1>(f)) { build(); }
    template<typename InputIt, typename F1 = F, typename iterator_traits<InputIt>::value_type* = nullptr>
    segtree(InputIt first, InputIt last, F1&& f = F1()) : base(first, last), f_(forward<F1>(f)) { build(); }
    template<typename U>
    void set(size_t i, U&& x) {
        i += size_ - 1;
        tree_[i] = forward<T>(x);
        if (i == 0) return;
        size_t l = i;
        size_t r = i + 1;
        if (i == leftidx(parentidx(i)))
            r += r - l;
        else
            l -= r - l;
        for (i = parentidx(i); i > 0; i = parentidx(i)) {
            tree_[i] = f(tree_[leftidx(i)], tree_[rightidx(i)], l, mid(l, r), r);
            if (i == leftidx(parentidx(i)))
                r += r - l;
            else
                l -= r - l;
        }
        tree_[0] = f(tree_[leftidx(0)], tree_[rightidx(0)], l, mid(l, r), r);
    }
    T calc(size_t l, size_t r) const {
        T res = Id;
        stack<segnode> s; s.push({0, 0, size_});
        while (!s.empty()) {
            segnode node = s.top(); s.pop();
            if (node.r <= l || r <= node.l) continue;
            if (l <= node.l && node.r <= r) {
                res = f(res, tree_[node.i], l, node.l, node.r);
                continue;
            }
            size_t m = mid(node.l, node.r);
            s.push({rightidx(node.i), m, node.r});
            s.push({leftidx(node.i), node.l, m});
        }
        return res;
    }
    template<typename U, typename Compare>
    size_t findpref(const U& x, Compare cmp) const {
        if (!cmp(x, tree_[0])) return size_;
        return findpref(x, cmp, {0, 0, size_}, Id, 0);
    }
    template<typename U, typename Compare>
    size_t findpref(size_t l, const U& x, Compare cmp) const {
        segnode node{leafidx(l), l, l + 1};
        while (node.i > 0 && node.i == leftidx(parentidx(node.i))) {
            node.i = parentidx(node.i);
            node.r += node.r - node.l;
        }
        if (cmp(x, tree_[node.i]))
            return findpref(x, cmp, node, Id, l);
        T pref = tree_[node.i];
        while (node.i > 0) {
            size_t parent = parentidx(node.i);
            size_t parentright = rightidx(parent);
            if (node.i == parentright) {
                node.l -= node.r - node.l;
            } else {
                size_t m = node.r;
                node.r += node.r - node.l;
                if (cmp(x, f(pref, tree_[parentright], l, m, node.r)))
                    return findpref(x, cmp, {parentright, m, node.r}, pref, l);
                pref = f(pref, tree_[parentright], m, node.r);
            }
            node.i = parent;
        }
        return size_;
    }
    template<typename U, typename Compare>
    size_t findsuf(const U& x, Compare cmp) const {
        if (!cmp(x, tree_[0])) return 0;
        return findsuf(x, cmp, {0, 0, size_}, Id, size_);
    }
    template<typename U, typename Compare>
    size_t findsuf(size_t r, const U& x, Compare cmp) const {
        segnode node{leafidx(r - 1), r - 1, r};
        while (node.i > 0 && node.i == rightidx(parentidx(node.i))) {
            node.i = parentidx(node.i);
            node.l -= node.r - node.l;
        }
        if (cmp(x, tree_[node.i]))
            return findsuf(x, cmp, node, Id, r);
        T suf = tree_[node.i];
        while (node.i > 0) {
            size_t parent = parentidx(node.i);
            size_t parentleft = leftidx(parent);
            if (node.i == parentleft) {
                node.r += node.r - node.l;
            } else {
                size_t m = node.l;
                node.l -= node.r - node.l;
                if (cmp(x, f(tree_[parentleft], suf, node.l, m)))
                    return findsuf(x, cmp, {parentleft, node.l, m}, suf, r);
                suf = f(tree_[parentleft], suf, node.l, m);
            }
            node.i = parent;
        }
        return 0;
    }
    template<typename U, typename Compare, typename Action>
    void apply(size_t l, size_t r, const U& x, Compare cmp, Action action) const {
        stack<segnode> s; s.push({0, 0, size_});
        while (!s.empty()) {
            segnode node = s.top(); s.pop();
            if (node.r <= l || r <= node.l || !cmp(x, tree_[node.i])) continue;
            if (node.r - node.l == 1) {
                action(node.l);
                continue;
            }
            size_t m = mid(node.l, node.r);
            s.push({rightidx(node.i), m, node.r});
            s.push({leftidx(node.i), node.l, m});
        }
    }
};

template<typename Op>
struct idprop {
    pair<Op, Op> operator()(const Op& op) const {
        return {op, op};
    }
};

template<typename Op = long long, Op OpId = Op(0), typename FOp = plus<Op>, typename FProp = idprop<Op>>
class masssegtree : public segtreebase<Op, OpId> {
    using base = segtreebase<Op, OpId>;
private:
    using base::size_;
    using base::tree_;
    using base::leftidx;
    using base::rightidx;
    using base::parentidx;
    using base::leafidx;
    using base::mid;
    using typename base::segnode;
    FOp fop_;
    FProp fprop_;
    template<typename Op1 = Op>
    inline auto fop(const Op1& lhs, const Op& rhs, size_t, size_t) const -> decltype(fop_(lhs, rhs)) {
        return fop_(lhs, rhs);
    }
    template<typename Op1 = Op>
    inline auto fop(const Op1& lhs, const Op& rhs, size_t l, size_t r) const -> decltype(fop_(lhs, rhs, l, r)) {
        return fop_(lhs, rhs, l, r);
    }
    template<typename Op1 = Op>
    inline auto fprop(const Op1& op, size_t, size_t) const -> decltype(fprop_(op)) {
        return fprop_(op);
    }
    template<typename Op1 = Op>
    inline auto fprop(const Op1& op, size_t l, size_t r) const -> decltype(fprop_(op, l, r)) {
        return fprop_(op, l, r);
    }
    void propagate(const segnode& node) {
        auto [lop, rop] = fprop(tree_[node.i], node.l, node.r);
        size_t m = mid(node.l, node.r);
        Op& left = tree_[leftidx(node.i)];
        left = fop(left, lop, node.l, m);
        Op& right = tree_[rightidx(node.i)];
        right = fop(right, rop, m, node.r);
        tree_[node.i] = OpId;
    }
public:
    template<typename FOp1 = FOp, typename FProp1 = FProp, enable_if_t<is_same_v<remove_reference_t<FOp1>, FOp>>* = nullptr>
    explicit masssegtree(size_t n, FOp1&& fop = FOp1(), FProp1&& fprop = FProp1())
        : base(n), fop_(forward<FOp1>(fop)), fprop_(forward<FProp1>(fprop)) {}
    template<typename FOp1 = FOp, typename FProp1 = FProp>
    masssegtree(size_t n, const Op& init, FOp1&& fop = FOp1(), FProp1&& fprop = FProp1())
        : base(n, init), fop_(forward<FOp1>(fop)), fprop_(forward<FProp1>(fprop)) {}
    template<
        typename InputIt, typename FOp1 = FOp, typename FProp1 = FProp,
        typename iterator_traits<InputIt>::value_type* = nullptr>
    masssegtree(InputIt first, InputIt last, FOp1&& fop = FOp1(), FProp1&& fprop = FProp1())
        : base(first, last), fop_(forward<FOp1>(fop)), fprop_(forward<FProp1>(fprop)) {}
    template<typename U>
    void modify(size_t l, size_t r, const U& x) {
        stack<segnode> s; s.push({0, 0, size_});
        while (!s.empty()) {
            segnode node = s.top(); s.pop();
            if (node.r <= l || r <= node.l) continue;
            if (l <= node.l && node.r <= r) {
                tree_[node.i] = fop(tree_[node.i], x, node.l, node.r);
                continue;
            }
            propagate(node);
            size_t m = mid(node.l, node.r);
            s.push({rightidx(node.i), m, node.r});
            s.push({leftidx(node.i), node.l, m});
        }
    }
    Op get(size_t i) {
        segnode node{0, 0, size_};
        while (node.r - node.l > 1) {
            propagate(node);
            size_t m = mid(node.l, node.r);
            if (i < m) {
                node.i = leftidx(node.i);
                node.r = m;
            } else {
                node.i = rightidx(node.i);
                node.l = m;
            }
        }
        return tree_[node.i];
    }
};

template<typename T, typename Op>
struct rangenode {
    T val;
    Op op;
};

template<typename InputIt, typename Op, Op OpId>
struct rangenodeiter {
    using difference_type = ptrdiff_t;
    using value_type = rangenode<typename iterator_traits<InputIt>::value_type, Op>;
    using pointer = value_type*;
    using reference = value_type;
    using iterator_category = input_iterator_tag;
    InputIt it;
    Op opid;
    rangenodeiter(InputIt it) : it(it) {}
    reference operator*() const {
        return {*it, opid};
    }
    pointer operator->() const {
        return &*it;
    }
    rangenodeiter& operator++() {
        ++it;
        return *this;
    }
    rangenodeiter operator++(int) {
        rangenodeiter iter = *this;
        ++*this;
        return iter;
    }
    bool operator==(const rangenodeiter& other) const {
        return it == other.it;
    }
    bool operator!=(const rangenodeiter& other) const {
        return !(*this == other);
    }
};

template<
    typename T = long long, T Id = T(0), typename F = plus<T>,
    typename Op = T, Op OpId = Op(1), typename FOp = multiplies<Op>, typename FEval = FOp, typename FProp = idprop<Op>>
class rangesegtree : public segtreebase<rangenode<T, Op>, rangenode<T, Op>{Id, OpId}> {
    using base = segtreebase<rangenode<T, Op>, rangenode<T, Op>{Id, OpId}>;
private:
    using base::size_;
    using base::tree_;
    using base::leftidx;
    using base::rightidx;
    using base::parentidx;
    using base::leafidx;
    using base::mid;
    using typename base::segnode;
    F f_;
    FOp fop_;
    FEval feval_;
    FProp fprop_;
    template<typename T1 = T>
    inline auto f(const T1& lhs, const T& rhs, size_t, size_t, size_t) const -> decltype(f_(lhs, rhs)) {
        return f_(lhs, rhs);
    }
    template<typename T1 = T>
    inline auto f(const T1& lhs, const T& rhs, size_t l, size_t m, size_t r) const -> decltype(f_(lhs, rhs, l, m, r)) {
        return f_(lhs, rhs, l, m, r);
    }
    template<typename Op1 = Op>
    inline auto fop(const Op1& lhs, const Op& rhs, size_t, size_t) const -> decltype(fop_(lhs, rhs)) {
        return fop_(lhs, rhs);
    }
    template<typename Op1 = Op>
    inline auto fop(const Op1& lhs, const Op& rhs, size_t l, size_t r) const -> decltype(fop_(lhs, rhs, l, r)) {
        return fop_(lhs, rhs, l, r);
    }
    template<typename T1 = T>
    inline auto feval(const T1& lhs, const Op& rhs, size_t, size_t) const -> decltype(feval_(lhs, rhs)) {
        return feval_(lhs, rhs);
    }
    template<typename T1 = T>
    inline auto feval(const T1& lhs, const Op& rhs, size_t l, size_t r) const -> decltype(feval_(lhs, rhs, l, r)) {
        return feval_(lhs, rhs, l, r);
    }
    template<typename Op1 = Op>
    inline auto fprop(const Op1& op, size_t, size_t) const -> decltype(fprop_(op)) {
        return fprop_(op);
    }
    template<typename Op1 = Op>
    inline auto fprop(const Op1& op, size_t l, size_t r) const -> decltype(fprop_(op, l, r)) {
        return fprop_(op, l, r);
    }
    void build() {
        size_t l = 0;
        size_t r = 1;
        for (size_t i = tree_.size() - size_ - 1; i != static_cast<size_t>(-1); --i) {
            size_t len = r - l;
            if (l == 0) {
                l = size_ - len * 2;
                r = size_;
            } else {
                l -= len;
                r -= len;
            }
            tree_[i].val = f(tree_[leftidx(i)].val, tree_[rightidx(i)].val, l, mid(l, r), r);
        }
    }
    void propagate(const segnode& node) {
        auto [lop, rop] = fprop(tree_[node.i].op, node.l, node.r);
        size_t m = mid(node.l, node.r);
        rangenode<T, Op>& left = tree_[leftidx(node.i)];
        left.val = feval(left.val, lop, node.l, m);
        left.op = fop(left.op, lop, node.l, m);
        rangenode<T, Op>& right = tree_[rightidx(node.i)];
        right.val = feval(right.val, rop, m, node.r);
        right.op = fop(right.op, rop, m, node.r);
        tree_[node.i].op = OpId;
    }
    template<typename U, typename Compare>
    size_t findpref(const U& x, Compare cmp, segnode node, T pref, size_t l) {
        while (node.r - node.l > 1) {
            propagate(node);
            size_t left = leftidx(node.i);
            size_t m = mid(node.l, node.r);
            if (cmp(x, f(pref, tree_[left].val, l, node.l, m))) {
                node.i = left;
                node.r = m;
            } else {
                pref = f(pref, tree_[left].val, l, node.l, m);
                node.i = rightidx(node.i);
                node.l = m;
            }
        }
        return node.r;
    }
    template<typename U, typename Compare>
    size_t findsuf(const U& x, Compare cmp, segnode node, T suf, size_t r) {
        while (node.r - node.l > 1) {
            propagate(node);
            size_t right = rightidx(node.i);
            size_t m = mid(node.l, node.r);
            if (cmp(x, f(tree_[right].val, suf, m, node.r, r))) {
                node.i = right;
                node.l = m;
            } else {
                suf = f(tree_[right].val, suf, m, node.r, r);
                node.i = leftidx(node.i);
                node.r = m;
            }
        }
        return node.l;
    }
public:
    template<
        typename F1 = F, typename FOp1 = FOp, typename FEval1 = FEval, typename FProp1 = FProp,
        enable_if_t<is_same_v<remove_reference_t<F1>, F>>* = nullptr>
    explicit rangesegtree(size_t n, F1&& f = F1(), FOp1&& fop = FOp1(), FEval1&& feval = FEval1(), FProp1&& fprop = FProp1())
        : base(n), f_(forward<F1>(f)), fop_(forward<FOp1>(fop)), feval_(forward<FEval1>(feval)), fprop_(forward<FProp1>(fprop)) {}
    template<typename F1 = F, typename FOp1 = FOp, typename FEval1 = FEval, typename FProp1 = FProp>
    rangesegtree(size_t n, const T& init, F1&& f = F1(), FOp1&& fop = FOp1(), FEval1&& feval = FEval1(), FProp1&& fprop = FProp1())
        : base(n, {init, OpId})
        , f_(forward<F1>(f)), fop_(forward<FOp1>(fop)), feval_(forward<FEval1>(feval)), fprop_(forward<FProp1>(fprop))
    { build(); }
    template<
        typename InputIt, typename F1 = F, typename FOp1 = FOp, typename FEval1 = FEval, typename FProp1 = FProp,
        typename iterator_traits<InputIt>::value_type* = nullptr>
    rangesegtree(
        InputIt first, InputIt last,
        F1&& f = F1(), FOp1&& fop = FOp1(), FEval1&& feval = FEval1(), FProp1&& fprop = FProp1())
        : base(rangenodeiter<InputIt, Op, OpId>(first), rangenodeiter<InputIt, Op, OpId>(last))
        , f_(forward<F1>(f)), fop_(forward<FOp1>(fop)), feval_(forward<FEval1>(feval)), fprop_(forward<FProp1>(fprop))
    { build(); }
    void modify(size_t l, size_t r, const Op& x) {
        stack<pair<segnode, bool>> s; s.emplace(segnode{0, 0, size_}, false);
        while (!s.empty()) {
            const segnode& node = s.top().first;
            bool& ret = s.top().second;
            if (ret) {
                tree_[node.i].val =
                    f(tree_[leftidx(node.i)].val, tree_[rightidx(node.i)].val, node.l, mid(node.l, node.r), node.r);
                s.pop();
                continue;
            }
            if (node.r <= l || r <= node.l) {
                s.pop();
                continue;
            }
            if (l <= node.l && node.r <= r) {
                tree_[node.i].val = feval(tree_[node.i].val, x, node.l, node.r);
                tree_[node.i].op = fop(tree_[node.i].op, x, node.l, node.r);
                s.pop();
                continue;
            }
            ret = true;
            propagate(node);
            size_t m = mid(node.l, node.r);
            s.emplace(segnode{rightidx(node.i), m, node.r}, false);
            s.emplace(segnode{leftidx(node.i), node.l, m}, false);
        }
    }
    T calc(size_t l, size_t r) {
        T res = Id;
        stack<segnode> s; s.push({0, 0, size_});
        while (!s.empty()) {
            segnode node = s.top(); s.pop();
            if (node.r <= l || r <= node.l) continue;
            if (l <= node.l && node.r <= r) {
                res = f(res, tree_[node.i].val, l, node.l, node.r);
                continue;
            }
            propagate(node);
            size_t m = mid(node.l, node.r);
            s.push({rightidx(node.i), m, node.r});
            s.push({leftidx(node.i), node.l, m});
        }
        return res;
    }
    template<typename U, typename Compare>
    size_t findpref(const U& x, Compare cmp) {
        if (!cmp(x, tree_[0].val)) return 0;
        return findpref(x, cmp, {0, 0, size_}, Id, 0);
    }
    template<typename U, typename Compare>
    size_t findpref(size_t l, const U& x, Compare cmp) {
        segnode node{0, 0, size_};
        while (node.l < l) {
            propagate(node);
            size_t m = mid(node.l, node.r);
            if (l < m) {
                node.i = leftidx(node.i);
                node.r = m;
            } else {
                node.i = rightidx(node.i);
                node.l = m;
            }
        }
        if (cmp(x, tree_[node.i].val))
            return findpref(x, cmp, node, Id, l);
        T pref = tree_[node.i].val;
        while (node.i > 0) {
            size_t parent = parentidx(node.i);
            size_t parentright = rightidx(parent);
            if (node.i == parentright) {
                node.l -= node.r - node.l;
            } else {
                size_t m = node.r;
                node.r += node.r - node.l;
                if (cmp(x, f(pref, tree_[parentright].val, l, m, node.r)))
                    return findpref(x, cmp, {parentright, m, node.r}, pref, l);
                pref = f(pref, tree_[parentright].val, l, m, node.r);
            }
            node.i = parent;
        }
        return l;
    }
    template<typename U, typename Compare>
    size_t findsuf(const U& x, Compare cmp) {
        if (!cmp(x, tree_[0].val)) return size_;
        return findsuf(x, cmp, {0, 0, size_}, Id, size_);
    }
    template<typename U, typename Compare>
    size_t findsuf(size_t r, const U& x, Compare cmp) {
        segnode node{0, 0, size_};
        while (node.r > r) {
            propagate(node);
            size_t m = mid(node.l, node.r);
            if (r >= m) {
                node.i = rightidx(node.i);
                node.l = m;
            } else {
                node.i = leftidx(node.i);
                node.r = m;
            }
        }
        if (cmp(x, tree_[node.i].val))
            return findsuf(x, cmp, node, Id, r);
        T suf = tree_[node.i].val;
        while (node.i > 0) {
            size_t parent = parentidx(node.i);
            size_t parentleft = leftidx(parent);
            if (node.i == parentleft) {
                node.r += node.r - node.l;
            } else {
                size_t m = node.l;
                node.l -= node.r - node.l;
                if (cmp(x, f(tree_[parentleft].val, suf, node.l, m, r)))
                    return findsuf(x, cmp, {parentleft, node.l, m}, suf, r);
                suf = f(tree_[parentleft].val, suf, node.l, m, r);
            }
            node.i = parent;
        }
        return r;
    }
    template<typename U, typename Compare, typename Action>
    void apply(size_t l, size_t r, const U& x, Compare cmp, Action action) {
        stack<segnode> s; s.push({0, 0, size_});
        while (!s.empty()) {
            segnode node = s.top(); s.pop();
            if (node.r <= l || r <= node.l || !cmp(x, tree_[node.i].val)) continue;
            if (node.r - node.l == 1) {
                action(node.l);
                continue;
            }
            propagate(node);
            size_t m = mid(node.l, node.r);
            s.push({rightidx(node.i), m, node.r});
            s.push({leftidx(node.i), node.l, m});
        }
    }
};

using ll = long long;
using ull = unsigned long long;

const int mod = 1000000007;

void solve() {
    int n; cin >> n;
    vector<string> queries;
    while (queries.empty() || queries.back() != "E") cin >> queries.emplace_back();
    queries.pop_back();
    vector<int> rails;
    for (int i = 0; i < queries.size();) {
        if (queries[i] == "I") {
            rails.push_back(stoi(queries[i + 1]));
            rails.push_back(stoi(queries[i + 2]) + 1);
            i += 4;
        } else {
            i += 2;
        }
    }
    sort(rails.begin(), rails.end());
    rails.erase(unique(rails.begin(), rails.end()), rails.end());
    map<int, int> idx;
    for (int i = 0; i < rails.size(); ++i)
        idx[rails[i]] = i;
    struct segment {
        int sum, max;
    };
    auto merge = [](const segment& lhs, const segment& rhs) {
        return segment{lhs.sum + rhs.sum, max(lhs.max, lhs.sum + rhs.max)};
    };
    auto assign = [](int lhs, int rhs) {
        return rhs == numeric_limits<int>::max() ? lhs : rhs;
    };
    auto elevate = [&rails](const segment& lhs, int rhs, int l, int r) {
        if (rhs == numeric_limits<int>::max()) return lhs;
        int sum = rhs * (rails[r] - rails[l]);
        return segment{sum, rhs > 0 ? sum : 0};
    };
    rangesegtree<
        segment, segment{0, 0}, decltype(merge),
        int, numeric_limits<int>::max(), decltype(assign), decltype(elevate)>
        seg(rails.size() - 1, merge, assign, elevate);
    for (int i = 0; i < queries.size();) {
        if (queries[i] == "I") {
            int l = stoi(queries[i + 1]);
            int r = stoi(queries[i + 2]);
            int d = stoi(queries[i + 3]);
            seg.modify(idx[l], idx[r + 1], d);
            i += 4;
        } else {
            int h = stoi(queries[i + 1]);
            int res = seg.findpref(h, [](int x, const segment& pref) { return x < pref.max; });
            if (res == 0) {
                cout << n << "\n";
            } else {
                int sum = seg.calc(0, res).sum;
                int d = seg.calc(res - 1, res).sum / (rails[res] - rails[res - 1]);
                cout << rails[res] - 1 - (sum - h + d - 1) / d << "\n";
            }
            i += 2;
        }
    }
}

int main() {
#ifdef DEBUG
    freopen("input.txt", "r", stdin);
    using namespace chrono;
    auto start = high_resolution_clock::now();
#endif
    ios_base::sync_with_stdio(false); cin.tie(nullptr);
#ifdef TEST_CASES
    int t; cin >> t;
    for (int i = 1; i <= t; ++i) {
#ifdef GOOGLE
        cout << "Case #" << i << ": ";
#endif
#endif
        solve();
#ifdef TEST_CASES
    }
#endif
#ifdef DEBUG
    auto elapsed = duration_cast<milliseconds>(
        high_resolution_clock::now() - start).count();
    cout << "time: " << elapsed << "ms\n";
#endif
}
// g++ -Wall segtree.cpp -DDEBUG -std=c++2a -o segtree && segtree