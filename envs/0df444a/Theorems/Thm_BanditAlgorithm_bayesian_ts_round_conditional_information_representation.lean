-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_round_conditional_information_representation
-- name    : BanditAlgorithm.bayesian_ts_round_conditional_information_representation
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T00:46:04.64899+00:00
-- url     : https://prove2.me/theorems/49499ee4-1157-4ce7-bbc9-bd7ce8749b99
-- title:
--   Conditional information-ratio representation for one Thompson round
-- statement:
--   Fix a round $t$ of Bayesian Thompson sampling and let $\nu_t$ be the law of the history available before that round. There exist integrable functions $r_t(h)$ and $g_t(h)$—the conditional expected regret and conditional information gain—such that
--
--   $$
--   \mathbb E[\Delta_t]=\int r_t(h)\,\nu_t(dh),
--   $$
--
--   their squares and information gains are integrable, and almost surely
--
--   $$
--   r_t(h)^2\le \frac{k}{2}g_t(h).
--   $$
--
--   Moreover, their average information gain is bounded by the increase in mutual information about the optimal arm:
--
--   $$
--   \int g_t(h)\,\nu_t(dh)
--   \le I(A^*;H_{t+1})-I(A^*;H_t).
--   $$
--
--   This is the rigorous conditional-law and Bayes-chain-rule core of Lemma 36.7. It keeps the posterior weights $p_h(a)$ inside the history integral, as required by the source proof.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 (free PDF p. 479), https://tor-lattimore.com/downloads/book/book.pdf; conditional-law and Bayes-law formalization.

import Definitions.Def_BayesianHistoryMutualInformation
import Mathlib.Analysis.Convex.Integral

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-- Conditional regret and information-gain functions for one Thompson-sampling round. -/
theorem bayesian_ts_round_conditional_information_representation
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi) (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    ∃ regretGain informationGain : BanditHistory k t.1 → ℝ,
      Integrable regretGain nu ∧
      Integrable (fun h ↦ regretGain h ^ 2) nu ∧
      Integrable informationGain nu ∧
      (∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
          ∂bayesianAdversarialMeasure Q pi n le_rfl) = ∫ h, regretGain h ∂nu ∧
      (∀ᵐ h ∂nu, regretGain h ^ 2 ≤ ((k : ℝ) / 2) * informationGain h) ∧
      (∫ h, informationGain h ∂nu) ≤
        bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
          bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2) := by
  sorry

end BanditAlgorithm
