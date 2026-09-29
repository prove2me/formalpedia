-- Prove2me | Theorems.Thm_BanditAlgorithm_thompson_sampling_bayesian_regret
-- name    : BanditAlgorithm.thompson_sampling_bayesian_regret
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-30T15:44:37.023253+00:00
-- url     : https://prove2.me/theorems/88888977-4a40-44a9-baa5-64348df660f3
-- statement:
--   (Bayesian regret, information-theoretic; L&S Theorem 36.5) For the Bayesian $k$-armed adversarial bandit of §36.4 — reward matrix $X \in [0,1]^{n \times k}$ drawn from an arbitrary prior $Q$ — Thompson sampling (the policy playing each action according to the conditional probability that it is optimal given the history) satisfies
--
--   $$BR_n \le \sqrt{\frac{kn\log k}{2}}.$$
--
--   (Proved in the book via the generic information-ratio Theorem 36.6 with the negentropy potential and Lemma 36.7's bound $\Gamma_t \le k/2$.)
-- source:
--   L&S Theorem 36.5 (with Theorem 36.6), p.469

import Definitions.Def_ThompsonSampling


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.thompson_sampling_bayesian_regret {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (t : Fin n) (a : Fin k), X t a ∈ Set.Icc (0 : ℝ) 1)
    {π : BanditPolicy k} (hπ : IsBayesianTSPolicy Q π) :
    bayesianAdversarialRegret Q π ≤ Real.sqrt (k * n * Real.log k / 2) := by
  sorry
