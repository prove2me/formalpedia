-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_Supplement_expected_regret
-- name    : BestBothWorlds.SAO.Supplement.expected_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:17:12.464835+00:00
-- url     : https://prove2.me/theorems/7aee46af-fe94-44b6-b856-307be3c96845
-- title:
--   Theorem 1.1 — SAO expected regret in both models
-- statement:
--   There are positive absolute constants $A,B$ such that for every $n\ge K\ge2$, SAO (Algorithm 1) with $\beta=n^4$ has
--
--   $$\mathbb E[R_n]\le A\sqrt{nK}\log^{3/2}(n)\log K,\qquad
--   \mathbb E[\overline R_n]\le B\frac{K}{\Delta}\log^2(n)\log K.$$
--
--   The first assertion covers every bounded adaptive adversary. The second covers every family of arm reward distributions on $[0,1]$ with a positive arm gap, with independent reward draws. When all means are equal the pseudo-regret and its expectation are zero. Both constants precede the arm count, horizon, adversary and reward distributions. The expectations use the published interaction law: a finite weighted sum over arm paths, and in the stochastic model an integral over the independent reward table.
--
--   This restores Theorem 1.1 in full and also states the expectation display of Theorem 4.1 (p. 12), which the published high-probability goal does not include. It is a companion theorem and is not an input to that goal.
--
--   **Formalization Note** The minimum positive gap is used only when a suboptimal arm exists. The all-equal case is stated separately. The SAO policy is fixed by its published definition, rather than quantified with regret bounds among its assumptions.
--
--   Differences from the source:
--   - encoding: O(·) expectation bounds for Algorithm 1 → Two positive absolute constants A and B quantified before all instances; SAO with β=n^4; reason: The usual uniform meaning of the source big-O notation; p. 12 specifies the expectation parameter
--   - encoding: Expected regret and expected pseudo-regret → Finite sums weighted by pathProb, and the integral of the stochastic path sum against rewardTableMeasure; reason: These are expectations under the published interaction law, without extra integrability premises
--   - generalization: Gap-dependent bound with Δ the minimum positive gap → The positive-gap bound together with zero expectation when every arm gap is zero; reason: The minimum is used on its source domain; the extra equal-mean clause explicitly covers the boundary where every pseudo-regret summand is zero
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 3, Theorem 1.1; also p. 12, Theorem 4.1 expectation display

import Mathlib
import Definitions.Def_BestBothWorlds_SAO_Interaction
import Definitions.Def_BestBothWorlds_SAO_Algorithm

open MeasureTheory

namespace BestBothWorlds.SAO.Supplement

/-- Theorem 1.1 (p. 3), also the expectation display of Theorem 4.1 (p. 12).
The two constants are absolute: they precede the horizon, arm count, and instances.
SAO is run with exactly the expectation theorem's parameter `β = n^4`.
For equal arm means the pseudo-regret is zero; the gap-dependent assertion is made
when the source's minimum over positive gaps is defined. -/
theorem expected_regret :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    ∀ K n : ℕ, 2 ≤ K → K ≤ n →
      (∀ adv : Adversary K, adv.IsBounded →
        (∑ I : Fin n → Fin K,
          pathProb (sao K n ((n : ℝ) ^ 4)) adv I * regret adv I) ≤
          A * Real.sqrt ((n : ℝ) * K) * Real.log (n : ℝ) ^ (3 / 2 : ℝ) *
            Real.log (K : ℝ)) ∧
      (∀ (ν : Fin K → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)],
        (∀ i, ν i (Set.Icc 0 1)ᶜ = 0) →
        let E : ℝ := ∫ ω,
          (∑ I : Fin n → Fin K,
            pathProb (sao K n ((n : ℝ) ^ 4)) (tableAdv ω) I *
              pseudoRegret (mean ν) I) ∂(rewardTableMeasure n ν)
        ((∃ i, 0 < gap (mean ν) i) →
          E ≤ B * (K : ℝ) / minGap (mean ν) * Real.log (n : ℝ) ^ 2 *
            Real.log (K : ℝ)) ∧
        ((∀ i, gap (mean ν) i = 0) → E = 0)) := by sorry

end BestBothWorlds.SAO.Supplement
