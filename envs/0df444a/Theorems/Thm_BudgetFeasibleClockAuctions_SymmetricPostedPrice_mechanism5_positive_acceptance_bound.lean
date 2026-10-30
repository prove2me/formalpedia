-- Prove2me | Theorems.Thm_BudgetFeasibleClockAuctions_SymmetricPostedPrice_mechanism5_positive_acceptance_bound
-- name    : BudgetFeasibleClockAuctions.SymmetricPostedPrice.mechanism5_positive_acceptance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:34:15.509975+00:00
-- url     : https://prove2.me/theorems/a4b9ecb1-bda0-4826-8d4f-a42c98876a96
-- title:
--   Theorem 15 proof, Case 2 — positive acceptances (corrected: reserve tail and strictness)
-- statement:
--   Let $N$ have $n$ bidders, let the public budget be $B$, let $0\le c_i\le B$ be their real costs, and choose any reserve $j\in N$. Bidders are processed in any public order. Acceptance includes equality. Use Mechanism 5 with the proof-consistent fallback acquisition, and write $(W,p)$ for its final winning set and offered-price record. Only $p_i$ for $i\in W$ is paid. A chosen reserve entails $n\ge1$ and affordability entails $B\ge0$; singleton and zero-budget instances remain included.
--
--   Let $v$ be symmetric submodular: there are $r_1\ge\cdots\ge r_n\ge0$ with $v(S)=\sum_{t=1}^{|S|}r_t$ for every subset $S$. A set $O\subseteq N$ is true-cost-feasible when $\sum_{i\in O}c_i\le B$; this benchmark includes the reserve.
--
--   Suppose the complete scan has $k\ge1$ acceptances; $k$ is its computed count. Let $W'$ and $p'$ be its winners and offered-price record. Then $W=W'$, $|W|=k\le n-1$, and every rejected scanned bidder $i\ne j$ satisfies
--
--   $$\frac{B}{2k\ln n}\le p'_i<c_i.$$
--
--   There is a marginal sequence representing $v$, decreasing and nonnegative at every index from $1$ to $n$, for which
--
--   $$v(W)=\sum_{t=1}^k r_t\ge k r_k,$$
--   $$v(O)\le v(W)+(2k\ln n+1)r_k
--   \le(1+2\ln n+1/k)v(W)
--   \le(2+2\ln n)v(W)$$
--
--   for every true-cost-feasible $O$, including sets containing the unqueried reserve. The extra marginal is necessary even when the reserve has cost zero. The formulas cover $B=0$ and all-zero marginals. This statement supplies the full positive-acceptance welfare chain and its offer comparison for the computed run.
--
--   Differences from the source:
--   - correction: Mechanism 5 line 13 offers B to j but does not update W → insert j and pay its accepted fallback offer when the scan count is zero; reason: Case 1 explicitly returns j; n=4, B=1, all costs and marginals 1 give empty output under the literal code but OPT=1
--   - correction: Case 2 omits the unqueried reserve and concludes factor 1+2 ln n → v(O)≤v(W)+(2k ln n+1)r_k≤(1+2 ln n+1/k)v(W)≤(2+2 ln n)v(W); reason: n=4, B=1, unit marginals, main costs (0,2/5,2/5) and reserve cost 0 give k=1, v(W)=1, OPT=4>1+2 ln 4; the added marginal counts precisely the reserve
--   - correction: Case 2 compares earlier offers strictly and uses equalities and strict ratios divided by r_k and v(W) → earlier offers are weakly larger; the welfare chain consists of non-strict cross-multiplied inequalities with division only by k≥1; reason: the a=0 and a=1 offers coincide; all-zero marginals give r_k=v(W)=0 on valid instances, so division by values is not defined in the source
--   - reading: Mechanism 5 input calls the valuation additive → the full symmetric submodular class, including nonconstant marginals; reason: the heading, section definition, Theorem 15 and its proof specify this class
--   - reading: section B.2 writes S ⊆ 2^N → S is a subset of N; reason: the declared domain v:2^N→ℝ≥0 and section 2 determine the intended type
--   - reading: Case 2 sums to the generally nonintegral endpoint 2k ln n+k → a tail bound for actual finite feasible subsets with k equal to the computed scan count; reason: only existing marginals are accessed; the reserve correction applies to the cardinality bound
--   - encoding: an arbitrarily ordered nonempty finite bidder set and arbitrary reserve → Fin n in increasing label order, universally quantified costs and reserve j:Fin n; reason: every public order is represented by relabeling; j entails n≥1 and 0≤c_j≤B entails B≥0, without excluding n=1 or B=0
--   - encoding: nonnegative v(S)=sum of the first |S| decreasing nonnegative marginals r_1,...,r_n → the published IsSymmetricSubmodular n v predicate on real-valued finite-set functions, with r(t) storing r_(t+1); reason: the predicate supplies exactly the source representation; indices ≥n are irrelevant and zero marginals and ties remain included
--   - encoding: pay the accepted offer to every winner → sum the published offered-price record only over computed winners; reason: the record also contains rejected offers; actual payment is that record on W and zero outside W
--   - encoding: OPT is the maximum value of a true-cost-feasible subset of all bidders → the welfare inequality holds for every O⊆Fin n with sum of c_i over O at most B, including O containing j; reason: the family is finite and nonempty because B≥0; this is equivalent to the attained optimal-value bound and assumes no optimality certificate
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, §B.2, Theorem 15 proof, Case 2 final unnumbered display, printed p. 28, PDF p. 29; Mechanism 5, printed p. 27, PDF p. 28; standing model §2, printed p. 5, PDF p. 6; symmetric valuation §B.2, printed p. 25, PDF p. 26

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting
import Theorems.Thm_BudgetClock_PostedSym_case_2

open BudgetClock.PostedSym

namespace BudgetFeasibleClockAuctions.SymmetricPostedPrice

/-- arXiv:2107.09239v2, Theorem 15 proof, Case 2, printed p. 28 / PDF p. 29.
Corrected: the unqueried reserve contributes one extra marginal to the benchmark tail.
Earlier offers are only weakly larger; use non-strict cross-multiplied bounds, allowing
zero marginals and B = 0. The witness r is exactly that of IsSymmetricSubmodular. -/
theorem mechanism5_positive_acceptance_bound (n : ℕ) (v : Finset (Fin n) → ℝ)
    (hv : IsSymmetricSubmodular n v) (B : ℝ) (c : Fin n → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B) (j : Fin n)
    (hsome : 1 ≤ (scan n B c j).count) :
    let s := scan n B c j
    let k := s.count
    let W := (mech5 n B c j).1
    W = s.winners ∧ W.card = k ∧ k ≤ n - 1 ∧
    (∀ i : Fin n, i ≠ j → i ∉ W →
      B / ((k : ℝ) * 2 * Real.log n) ≤ s.price i ∧ s.price i < c i) ∧
    ∃ r : ℕ → ℝ,
      (∀ t, t < n → 0 ≤ r t) ∧
      (∀ t u, t ≤ u → u < n → r u ≤ r t) ∧
      (∀ S : Finset (Fin n), v S = ∑ t ∈ Finset.range S.card, r t) ∧
      v W = (∑ t ∈ Finset.range k, r t) ∧
      (k : ℝ) * r (k - 1) ≤ v W ∧
      ∀ O : Finset (Fin n), (∑ i ∈ O, c i) ≤ B →
        v O ≤ v W + (2 * (k : ℝ) * Real.log n + 1) * r (k - 1) ∧
        v W + (2 * (k : ℝ) * Real.log n + 1) * r (k - 1) ≤
          (1 + 2 * Real.log n + 1 / (k : ℝ)) * v W ∧
        (1 + 2 * Real.log n + 1 / (k : ℝ)) * v W ≤
          (2 + 2 * Real.log n) * v W := by sorry

end BudgetFeasibleClockAuctions.SymmetricPostedPrice
