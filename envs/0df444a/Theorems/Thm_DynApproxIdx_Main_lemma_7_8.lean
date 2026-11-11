-- Prove2me | Theorems.Thm_DynApproxIdx_Main_lemma_7_8
-- name    : DynApproxIdx.Main.lemma_7_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:52:11.727308+00:00
-- url     : https://prove2.me/theorems/a390b6d8-23ca-4e26-a315-c7faaef18d34
-- title:
--   Lemma 7.8 — shifting X by one period does not increase the edit distance when the clutter is (kq)-far
-- statement:
--   Let $k\ge1$ and let $X,Y$ be strings with $\delta_E(X,Y)\le k$. Let $Q$ be a primitive string of length $q$, and let $X=\bigodot_{j=0}^{t}X_j$ and $Y=\bigodot_{j=0}^{r}Y_j$ be $Q$-decompositions (Definition 7.3) such that
--   - $Q^{4k}$ is a suffix of $X_0$ and a prefix of $X_t$, and
--   - $X$ and $Y$ are $(kq)$-far with respect to these decompositions (Definition 7.4).
--
--   Then, for $X'=X[q..|X|)\odot X[|X|-q..|X|)$,
--   $$\delta_E(X',Y)\le\delta_E(X,Y).$$
--   It is the edit-distance counterpart of Lemma 7.5 (the lengths of $X$ and $Y$ may differ), used to bound the anchors the index stores in periodic regions.
--
--   Differences from the source:
--
--   - encoding: strings over the integer alphabet Σ, 0-based positions; δ_E the minimum number of insertions, deletions and substitutions → List ℕ; PMEdits.Main.ed, the minimum cost of an alignment-graph path from (0,0) to (|U|,|V|); reason: the standard bijection between edit sequences and alignment-graph paths; same values
--   - encoding: Q-decompositions X = ⊙^t_{j=0} X_j, Y = ⊙^r_{j=0} Y_j (Definition 7.3), with X_i = X[a_i..b_i) → lists Xs, Ys of factors with IsQDecomp Q X Xs (nonempty, concatenation X, the four clauses of Definition 7.3); a_i, b_i are prefix sums of factor lengths (startPos, endPos); reason: a decomposition is its list of factors
--   - encoding: X and Y are (kq)-far (Definition 7.4): [a_i − 12kq..b_i + 12kq) ∩ [a′_j..b′_j) = ∅ for odd i ∈ (0..t), j ∈ (0..r) → IsFar (k * Q.length) Xs Ys: no integer x lies in both intervals, computed in ℤ; reason: a_i − 12kq may be negative; integer intervals keep it exact
--   - encoding: Q^{4k} is a suffix of X_0 and a prefix of X_t → qpow Q (4k) <:+ Xs.headD [] and qpow Q (4k) <+: Xs.getLastD []; reason: Xs is nonempty (IsQDecomp), so headD and getLastD are X_0 and X_t
--   - encoding: X′ = X[q..|X|) ⊙ X[|X| − q..|X|) → shiftQ X q = frag X q |X| ++ frag X (|X| − q) |X|; reason: the hypotheses force |X| ≥ 4kq ≥ q, so both fragments are the printed ones
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), p. 32 (PDF 34), Lemma 7.8

import Mathlib
import Definitions.Def_PMEdits_Main_Strings
import Definitions.Def_DynApproxIdx_Main_Periodic

namespace DynApproxIdx.Main

open PMEdits.Main

/-- **Lemma 7.8** (Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC
2027 submission, p. 32 (PDF 34)). Let `k ≥ 1` and let `X`, `Y` be strings with `δ_E(X, Y) ≤ k`.
Let `Q` be a primitive string of length `q`, and let `X = ⊙_{j=0}^t X_j` and `Y = ⊙_{j=0}^r Y_j`
be `Q`-decompositions such that `Q^{4k}` is a suffix of `X_0` and a prefix of `X_t`, and `X`, `Y`
are `(kq)`-far with respect to them. Then `δ_E(X′, Y) ≤ δ_E(X, Y)` for
`X′ = X[q..|X|) ⊙ X[|X|−q..|X|)`. -/
theorem lemma_7_8 (k : ℕ) (hk : 1 ≤ k) (X Y : List ℕ) (hE : ed X Y ≤ k)
    (Q : List ℕ) (hQ : Primitive Q) (Xs Ys : List (List ℕ))
    (hXs : IsQDecomp Q X Xs) (hYs : IsQDecomp Q Y Ys)
    (h0 : qpow Q (4 * k) <:+ Xs.headD []) (ht : qpow Q (4 * k) <+: Xs.getLastD [])
    (hfar : IsFar (k * Q.length) Xs Ys) :
    ed (shiftQ X Q.length) Y ≤ ed X Y := by sorry

end DynApproxIdx.Main
