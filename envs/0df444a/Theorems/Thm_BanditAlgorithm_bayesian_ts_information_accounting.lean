-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_information_accounting
-- name    : BanditAlgorithm.bayesian_ts_information_accounting
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T21:42:40.344372+00:00
-- url     : https://prove2.me/theorems/f7844286-ecc7-474b-b1a2-b8ecff214fb9
-- title:
--   Bayesian Thompson sampling information accounting
-- statement:
--   Consider a Bayesian adversarial $k$-armed bandit over $n$ rounds. A reward matrix $X\in[0,1]^{n\times k}$ is drawn from an arbitrary prior $Q$, and Thompson sampling plays according to the posterior distribution of the best fixed action $A^*$. Then there are per-round expected-regret terms $\delta_t$ and per-round information gains $I_t$ such that
--
--   $$
--   BR_n=\sum_{t=1}^n\delta_t,
--   \qquad
--   \delta_t^2\le\frac{k}{2}I_t,
--   \qquad
--   \sum_{t=1}^n I_t\le\log k.
--   $$
--
--   The pointwise inequality is the Thompson-sampling information-ratio estimate, while the last inequality is the chain-rule bound $I(A^*;H_n)\le H(A^*)\le\log k$. This theorem isolates the probabilistic and information-theoretic core from the final Cauchy--Schwarz step.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Theorem 36.5, Theorem 36.6, and Lemma 36.7, printed pp. 469-473; Eq. (36.10) and the proof of Lemma 36.7.

import Definitions.Def_ThompsonSampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem BanditAlgorithm.bayesian_ts_information_accounting {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (t : Fin n) (a : Fin k), X t a ∈ Set.Icc (0 : ℝ) 1)
    {π : BanditPolicy k} (hπ : IsBayesianTSPolicy Q π) :
    ∃ δ info : Fin n → ℝ,
      bayesianAdversarialRegret Q π = ∑ t, δ t ∧
      (∀ t, δ t ^ 2 ≤ ((k : ℝ) / 2) * info t) ∧
      ∑ t, info t ≤ Real.log k := by
  sorry
