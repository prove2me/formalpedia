-- Prove2me | Theorems.Thm_BudgetFeasibleClockAuctions_SymmetricPostedPrice_mechanism5_no_acceptance_bound
-- name    : BudgetFeasibleClockAuctions.SymmetricPostedPrice.mechanism5_no_acceptance_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:33:37.040736+00:00
-- url     : https://prove2.me/theorems/03504177-4a0b-4f5a-8811-2e4c60ce1a14
-- title:
--   Theorem 15 proof, Case 1 — no acceptances (corrected: reserve and non-strict bound)
-- statement:
--   Let $N$ have $n$ bidders, let the public budget be $B$, let $0\le c_i\le B$ be their real costs, and choose any reserve $j\in N$. Bidders are processed in any public order. Acceptance includes equality. Use Mechanism 5 with the proof-consistent fallback acquisition, and write $(W,p)$ for its final winning set and offered-price record. Only $p_i$ for $i\in W$ is paid. A chosen reserve entails $n\ge1$ and affordability entails $B\ge0$; singleton and zero-budget instances remain included.
--
--   Let $v$ be symmetric submodular: there are $r_1\ge\cdots\ge r_n\ge0$ with $v(S)=\sum_{t=1}^{|S|}r_t$ for every subset $S$. A set $O\subseteq N$ is true-cost-feasible when $\sum_{i\in O}c_i\le B$; this benchmark includes the reserve.
--
--   Suppose the complete scan has no acceptances. Then
--
--   $$W=\{j\},\qquad\sum_{i\in W}p_i=B,\qquad
--   v(O)\le(1+2\ln n)v(W)\quad\text{for every true-cost-feasible }O.$$
--
--   Here $v(W)=r_1$ for any representing marginal sequence. At $n=1$ the feasible singleton attains $v(W)$ exactly. When $B=0$ and $n\ge2$, the zero-count premise cannot hold, since every scanned zero-cost bidder accepts its zero offer. No global budget-positivity restriction is added. This is the complete zero-acceptance case used by the approximation theorem, retaining zero-valued welfare without ratios.
--
--   Differences from the source:
--   - correction: Mechanism 5 line 13 offers B to j but does not update W → insert j and pay its accepted fallback offer when the scan count is zero; reason: Case 1 explicitly returns j; n=4, B=1, all costs and marginals 1 give empty output under the literal code but OPT=1
--   - correction: Case 1 equates OPT/v(M) with an upper bound and concludes a strict ratio bound → v(O)≤(1+2 ln n)v(W) for every true-cost-feasible O, without dividing by values; reason: zero marginals make the ratio undefined; n=1, B=1, cost 1 and marginal 1 give OPT=v(W)=1, refuting strictness; the displayed equality is only an upper bound
--   - reading: Mechanism 5 input calls the valuation additive → the full symmetric submodular class, including nonconstant marginals; reason: the heading, section definition, Theorem 15 and its proof specify this class
--   - reading: section B.2 writes S ⊆ 2^N → S is a subset of N; reason: the declared domain v:2^N→ℝ≥0 and section 2 determine the intended type
--   - reading: Case 1 sums to the generally nonintegral upper endpoint 2 ln n+1 → a welfare bound for every actual finite cost-feasible subset; reason: the source gives no floor convention or extension of the n marginals; no such convention is required
--   - reading: Case 1 says each agent rejects the initial offer → the zero-count premise concerns only scanned bidders; the affordable reserve accepts B; reason: j is set aside from the loop and is not subject to its rejection lower bound
--   - encoding: an arbitrarily ordered nonempty finite bidder set and arbitrary reserve → Fin n in increasing label order, universally quantified costs and reserve j:Fin n; reason: every public order is represented by relabeling; j entails n≥1 and 0≤c_j≤B entails B≥0, without excluding n=1 or B=0
--   - encoding: nonnegative v(S)=sum of the first |S| decreasing nonnegative marginals r_1,...,r_n → the published IsSymmetricSubmodular n v predicate on real-valued finite-set functions, with r(t) storing r_(t+1); reason: the predicate supplies exactly the source representation; indices ≥n are irrelevant and zero marginals and ties remain included
--   - encoding: pay the accepted offer to every winner → sum the published offered-price record only over computed winners; reason: the record also contains rejected offers; actual payment is that record on W and zero outside W
--   - encoding: OPT is the maximum value of a true-cost-feasible subset of all bidders → the welfare inequality holds for every O⊆Fin n with sum of c_i over O at most B, including O containing j; reason: the family is finite and nonempty because B≥0; this is equivalent to the attained optimal-value bound and assumes no optimality certificate
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, §B.2, Theorem 15 proof, Case 1 final unnumbered display, printed p. 28, PDF p. 29; Mechanism 5, printed p. 27, PDF p. 28; standing model §2, printed p. 5, PDF p. 6; symmetric valuation §B.2, printed p. 25, PDF p. 26

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting
import Theorems.Thm_BudgetClock_PostedSym_case_1

open BudgetClock.PostedSym

namespace BudgetFeasibleClockAuctions.SymmetricPostedPrice

/-- arXiv:2107.09239v2, Theorem 15 proof, Case 1, printed p. 28 / PDF p. 29.
Corrected: acquire the accepting reserve and cross multiply the non-strict welfare bound.
No positivity of values or budget and no lower bound n >= 2 are imposed. -/
theorem mechanism5_no_acceptance_bound (n : ℕ) (v : Finset (Fin n) → ℝ)
    (hv : IsSymmetricSubmodular n v) (B : ℝ) (c : Fin n → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B) (j : Fin n)
    (hnone : (scan n B c j).count = 0) :
    (mech5 n B c j).1 = {j} ∧
    (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i) = B ∧
    ∀ O : Finset (Fin n), (∑ i ∈ O, c i) ≤ B →
      v O ≤ (1 + 2 * Real.log n) * v (mech5 n B c j).1 := by sorry

end BudgetFeasibleClockAuctions.SymmetricPostedPrice
