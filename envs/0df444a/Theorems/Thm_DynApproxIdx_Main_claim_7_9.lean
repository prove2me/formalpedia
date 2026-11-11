-- Prove2me | Theorems.Thm_DynApproxIdx_Main_claim_7_9
-- name    : DynApproxIdx.Main.claim_7_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:52:32.022051+00:00
-- url     : https://prove2.me/theorems/5fd7c12a-4f89-4e76-ae56-da24e6d204ec
-- title:
--   Claim 7.9 — under Lemma 7.8's hypotheses, an optimal alignment splits into pairs with exact copies of Q at odd indices
-- statement:
--   Assume the hypotheses of Lemma 7.8: $k\ge1$, strings $X,Y$ with $\delta_E(X,Y)\le k$, a primitive string $Q$ of length $q$, and $Q$-decompositions $X=\bigodot_{j=0}^{t}X_j$, $Y=\bigodot_{j=0}^{r}Y_j$ such that $Q^{4k}$ is a suffix of $X_0$ and a prefix of $X_t$ and $X,Y$ are $(kq)$-far with respect to them. Then there is a sequence $(U_0,V_0),\dots,(U_s,V_s)$ of pairs of strings with $s$ even such that
--   1. $X=\bigodot_{j=0}^{s}U_j$ and $Y=\bigodot_{j=0}^{s}V_j$;
--   2. $$\delta_E(X,Y)=\sum_{i=0}^{s}\delta_E(U_i,V_i);$$
--   3. $U_i=V_i=Q$ for every odd $i$;
--   4. for every even $i\in(0..s)$, at least one of $U_i,V_i$ is a power of $Q$.
--
--   The claim is the decomposition step inside the proof of Lemma 7.8.
--
--   **Formalization Note.** A power of $Q$ includes $Q^0=\varepsilon$; $i\in(0..s)$ excludes $0$ and $s$. See the mission's insight I1: the four properties as printed do not by themselves give the decomposition of $X'$ used right after the claim; the claim is stated as printed.
--
--   Differences from the source:
--
--   - encoding: strings over the integer alphabet Σ, 0-based positions; δ_E the minimum number of insertions, deletions and substitutions → List ℕ; PMEdits.Main.ed, the minimum cost of an alignment-graph path from (0,0) to (|U|,|V|); reason: the standard bijection between edit sequences and alignment-graph paths; same values
--   - encoding: Q-decompositions X = ⊙^t_{j=0} X_j, Y = ⊙^r_{j=0} Y_j (Definition 7.3), with X_i = X[a_i..b_i) → lists Xs, Ys of factors with IsQDecomp Q X Xs (nonempty, concatenation X, the four clauses of Definition 7.3); a_i, b_i are prefix sums of factor lengths (startPos, endPos); reason: a decomposition is its list of factors
--   - encoding: X and Y are (kq)-far (Definition 7.4): [a_i − 12kq..b_i + 12kq) ∩ [a′_j..b′_j) = ∅ for odd i ∈ (0..t), j ∈ (0..r) → IsFar (k * Q.length) Xs Ys: no integer x lies in both intervals, computed in ℤ; reason: a_i − 12kq may be negative; integer intervals keep it exact
--   - encoding: Q^{4k} is a suffix of X_0 and a prefix of X_t → qpow Q (4k) <:+ Xs.headD [] and qpow Q (4k) <+: Xs.getLastD []; reason: Xs is nonempty (IsQDecomp), so headD and getLastD are X_0 and X_t
--   - encoding: Claim 7.9 inside the proof of Lemma 7.8, whose hypotheses are in force → Lemma 7.8's hypotheses as binders of the claim; reason: the claim is stated in that context; the proof's own assumption δ_E(X,Y) ≤ k is one of them
--   - encoding: a sequence (U_0,V_0),…,(U_s,V_s) with even s → a list UV of pairs of odd length (s = length − 1); reason: s even iff s + 1 odd
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), p. 32 (PDF 34), Claim 7.9 (in the proof of Lemma 7.8)

import Mathlib
import Definitions.Def_PMEdits_Main_Strings
import Definitions.Def_DynApproxIdx_Main_Periodic

namespace DynApproxIdx.Main

open PMEdits.Main

/-- **Claim 7.9** (Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC
2027 submission, p. 32 (PDF 34)), under the hypotheses of Lemma 7.8: `k ≥ 1`, `δ_E(X, Y) ≤ k`,
`Q` primitive of length `q`, `Q`-decompositions `X = ⊙_{j=0}^t X_j` and `Y = ⊙_{j=0}^r Y_j` with
`Q^{4k}` a suffix of `X_0` and a prefix of `X_t`, and `X`, `Y` `(kq)`-far with respect to them.
Then there is a sequence `(U_0, V_0), …, (U_s, V_s)` of pairs of strings with `s` even such that
1. `X = ⊙_{j=0}^s U_j` and `Y = ⊙_{j=0}^s V_j`;
2. `δ_E(X, Y) = Σ_{i=0}^s δ_E(U_i, V_i)`;
3. `U_i = V_i = Q` for every odd `i`;
4. for every even `i ∈ (0..s)`, at least one of `U_i`, `V_i` is a power of `Q` (`Q^0 = ε`
   included). -/
theorem claim_7_9 (k : ℕ) (hk : 1 ≤ k) (X Y : List ℕ) (hE : ed X Y ≤ k)
    (Q : List ℕ) (hQ : Primitive Q) (Xs Ys : List (List ℕ))
    (hXs : IsQDecomp Q X Xs) (hYs : IsQDecomp Q Y Ys)
    (h0 : qpow Q (4 * k) <:+ Xs.headD []) (ht : qpow Q (4 * k) <+: Xs.getLastD [])
    (hfar : IsFar (k * Q.length) Xs Ys) :
    ∃ UV : List (List ℕ × List ℕ), Odd UV.length ∧
      (UV.map Prod.fst).flatten = X ∧ (UV.map Prod.snd).flatten = Y ∧
      ed X Y = (UV.map fun p => ed p.1 p.2).sum ∧
      (∀ (i : ℕ) (hi : i < UV.length), Odd i → UV[i].1 = Q ∧ UV[i].2 = Q) ∧
      ∀ (i : ℕ) (hi : i < UV.length), Even i → 0 < i → i + 1 < UV.length →
        (∃ e : ℕ, UV[i].1 = qpow Q e) ∨ ∃ e : ℕ, UV[i].2 = qpow Q e := by sorry

end DynApproxIdx.Main
