-- Prove2me | Theorems.Thm_BanditAlgorithm_best_arm_identification_stopping_change_of_measure
-- name    : BanditAlgorithm.best_arm_identification_stopping_change_of_measure
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T18:58:04.617336+00:00
-- url     : https://prove2.me/theorems/bd1013c9-d5f9-431f-a14c-e07743214a3e
-- title:
--   Stopped change-of-measure inequality for best-arm identification
-- statement:
--   Let $(\pi,\tau,\psi)$ be a best-arm-identification strategy that is sound at confidence $\delta\in(0,1)$ on an environment class $\mathcal E$. Fix $\nu\in\mathcal E$ and an alternative $\nu'\in\mathcal E_{\mathrm{alt}}(\nu)$ whose optimal arms are disjoint from those of $\nu$. Assume the expected stopping time under $\nu$ is finite. If $T_i(\tau)$ denotes the number of pulls of arm $i$ strictly before the stopping time, then
--
--   $$
--   \log\!\frac{1}{4\delta}
--   \le
--   \sum_{i=1}^k \mathbb E_{\nu,\pi}[T_i(\tau)]\,
--   D(\nu_i\Vert\nu_i').
--   $$
--
--   The inequality is understood in $[0,\infty]$, so it also covers singular arm laws. This is the stopped-experiment information constraint used in every fixed-confidence best-arm-identification lower bound.
--
--   **Formalization Note** The stopped pull count is represented directly as the infinite sum of the indicators $\mathbf 1\{t<\tau, A_t=i\}$ on the canonical infinite trajectory.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 33.5 proof, printed p. 407, Eqs. (33.5)–(33.6), using the stopping-time version of Lemma 15.1 requested in Exercise 15.7, printed p. 211.

import Definitions.Def_BanditTrajectory

open MeasureTheory ProbabilityTheory InformationTheory ENNReal

theorem BanditAlgorithm.best_arm_identification_stopping_change_of_measure {k : ℕ}
    (𝓔 : Set (StochasticBandit k)) (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (π : BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin k × ℝ) → Fin k)
    (hτ : IsBanditStoppingTime τ) (hψ : Measurable[hτ.measurableSpace] ψ)
    (hsound : IsSoundBAI δ π τ ψ 𝓔)
    (ν ν' : StochasticBandit k) (hν : ν ∈ 𝓔)
    (hν' : ν' ∈ baiAlternatives 𝓔 ν)
    (hfinite : ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π < ⊤) :
    ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤
      ∑ i, (∫⁻ ω, ∑' t : ℕ,
          if (t : ℕ∞) < τ ω ∧ (ω t).1 = i then (1 : ℝ≥0∞) else 0
        ∂banditTrajMeasure ν π) * klDiv (ν.P i) (ν'.P i) := by
  sorry
