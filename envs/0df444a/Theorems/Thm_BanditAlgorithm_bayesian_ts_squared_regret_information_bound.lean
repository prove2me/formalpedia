-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_squared_regret_information_bound
-- name    : BanditAlgorithm.bayesian_ts_squared_regret_information_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T22:01:17.857843+00:00
-- url     : https://prove2.me/theorems/fbf38e86-7a1b-4488-ac92-f9848e2f1f38
-- title:
--   Squared instantaneous regret controlled by prior entropy
-- statement:
--   Consider the Bayesian adversarial $k$-armed bandit over $n$ rounds with an arbitrary prior on reward matrices in $[0,1]^{n\times k}$, and let Thompson sampling use the posterior distribution of the best fixed action. There are per-round conditional expected-regret terms $\delta_t$ which decompose Bayesian regret and satisfy
--
--   $$
--   BR_n=\sum_{t=1}^n\delta_t,
--   \qquad
--   \sum_{t=1}^n\delta_t^2\le\frac{k}{2}\log k.
--   $$
--
--   This combines the pointwise information-ratio estimate $\Gamma_t\le k/2$ with the mutual-information chain rule and the entropy bound $H(A^*)\le\log k$. It isolates the probabilistic core before the final Cauchy--Schwarz conversion from squared instantaneous regret to total regret.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Theorem 36.5, Theorem 36.6, and Lemma 36.7, printed pp. 469-473; Eq. (36.10) and the proof of Lemma 36.7.

import Definitions.Def_ThompsonSampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem BanditAlgorithm.bayesian_ts_squared_regret_information_bound {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (t : Fin n) (a : Fin k), X t a ∈ Set.Icc (0 : ℝ) 1)
    {π : BanditPolicy k} (hπ : IsBayesianTSPolicy Q π) :
    ∃ δ : Fin n → ℝ,
      bayesianAdversarialRegret Q π = ∑ t, δ t ∧
      ∑ t, δ t ^ 2 ≤ ((k : ℝ) / 2) * Real.log k := by
  sorry
