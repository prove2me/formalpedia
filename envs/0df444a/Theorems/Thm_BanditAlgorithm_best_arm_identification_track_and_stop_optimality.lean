-- Prove2me | Theorems.Thm_BanditAlgorithm_best_arm_identification_track_and_stop_optimality
-- name    : BanditAlgorithm.best_arm_identification_track_and_stop_optimality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-30T03:28:50.578633+00:00
-- url     : https://prove2.me/theorems/9e7c9391-aff0-40a9-99ac-2e042d404361
-- statement:
--   (Track-and-Stop asymptotic optimality, Theorem 33.6, GOAL) Over the class $\mathcal{E}=\mathcal{E}^k_{\mathcal{N}}(1)$ of unit-variance Gaussian bandits there exist a policy $\pi$ (independent of $\delta$) and, for each $\delta\in(0,1)$, a stopping time $\tau_\delta$ and an $\mathcal{F}_{\tau_\delta}$-measurable selection rule $\psi_\delta$ — Track-and-Stop, Algorithm 21, with the threshold $\beta_t(\delta)$ of Lemma 33.7 — such that each triple $(\pi,\tau_\delta,\psi_\delta)$ is sound at confidence $\delta$, and for every $\nu\in\mathcal{E}$ with a unique optimal arm,
--
--   $$\lim_{\delta\to 0^+} \frac{\mathbb{E}_{\nu\pi}[\tau_\delta]}{\log(1/\delta)} = c^*(\nu).$$
-- source:
--   L&S Theorem 33.6, p.410

import Definitions.Def_BanditTrajectory
import Definitions.Def_GaussianBandit


open MeasureTheory ProbabilityTheory Filter ENNReal

theorem BanditAlgorithm.best_arm_identification_track_and_stop_optimality {k : ℕ} (hk : 0 < k) :
    ∃ (π : BanditPolicy k) (τ : ℝ → (ℕ → Fin k × ℝ) → ℕ∞)
      (ψ : ℝ → (ℕ → Fin k × ℝ) → Fin k),
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1,
        ∃ hτ : IsBanditStoppingTime (τ δ),
          Measurable[hτ.measurableSpace] (ψ δ) ∧
            IsSoundBAI δ π (τ δ) (ψ δ) (Set.range (gaussianBandit (k := k)))) ∧
      ∀ ν ∈ Set.range (gaussianBandit (k := k)), (∃! i, i ∈ banditOptimalArms ν) →
        Tendsto
          (fun δ : ℝ ↦
            (∫⁻ ω, (τ δ ω : ℝ≥0∞) ∂banditTrajMeasure ν π).toReal / Real.log (1 / δ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (baiComplexity ν (Set.range (gaussianBandit (k := k)))).toReal) := by
  sorry
