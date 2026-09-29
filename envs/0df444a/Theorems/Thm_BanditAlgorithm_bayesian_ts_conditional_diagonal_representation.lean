-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_diagonal_representation
-- name    : BanditAlgorithm.bayesian_ts_conditional_diagonal_representation
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T03:18:36.91385+00:00
-- url     : https://prove2.me/theorems/1709aff1-e29d-40ef-b07e-4cf5de975404
-- title:
--   Posterior diagonal representation for the Thompson-sampling information ratio
-- statement:
--   Consider Bayesian Thompson sampling with $k$ actions and rewards in $[0,1]$. Fix a round $t$ and condition on the history $H_t=h$. Let $p_h(a)=\mathbb P(A^*=a\mid H_t=h)$. For almost every history, there are conditional reward laws $P_{h,a}$ (given $A^*=a$) and reference reward laws $M_{h,a}$ such that
--
--   $$
--   r_t(h)=\sum_a p_h(a)\left(\mathbb E_{P_{h,a}}[Y]-\mathbb E_{M_{h,a}}[Y]\right)
--   $$
--
--   and
--
--   $$
--   \sum_a p_h(a)^2D(P_{h,a}\|M_{h,a})\le I(A^*;(A_t,X_{t,A_t})\mid H_t=h).
--   $$
--
--   All displayed laws are probability measures and the divergences are finite. This is the posterior diagonal decomposition used in the information-ratio proof for Thompson sampling.
--
--   **Formalization Note** The reward laws are measures on the subtype $[0,1]$, which makes the bounded-reward hypotheses explicit.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 / free PDF p. 479, especially the posterior action probabilities and diagonal KL terms in the proof.

import Definitions.Def_BayesianTSRoundConditionalGains

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

namespace BanditAlgorithm

/-- Posterior diagonal representation in the conditional proof of the
Thompson-sampling information ratio. -/
theorem bayesian_ts_conditional_diagonal_representation
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi) (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    ∀ᵐ h ∂nu, ∃ (p : Fin k → ℝ)
      (P M : Fin k → Measure (Set.Icc (0 : ℝ) 1)),
      (∀ a, IsProbabilityMeasure (P a)) ∧
      (∀ a, IsProbabilityMeasure (M a)) ∧
      (∀ a, klDiv (P a) (M a) ≠ ∞) ∧
      bayesianTSRoundConditionalRegretGain Q pi t h =
        ∑ a, p a * ((∫ z, z.1 ∂P a) - ∫ z, z.1 ∂M a) ∧
      (∑ a, p a ^ 2 * (klDiv (P a) (M a)).toReal) ≤
        bayesianTSRoundConditionalInformationGain Q pi t h := by
  sorry

end BanditAlgorithm
