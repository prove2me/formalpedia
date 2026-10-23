-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_expectation_tendsto_full
-- name    : AvramDividend.Classical.chat03_actual_ceiling_capped_grid_expectation_tendsto_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:07:49.763994+00:00
-- url     : https://prove2.me/theorems/85c47988-662a-4b7a-a449-d92d47b4c53b
-- title:
--   Actual capped-grid stopped scale expectations converge with no measurability assumption
-- statement:
--   For the true uniform-mesh first-exit indices capped at finite horizon T, the discounted q-scale rewards converge in expectation to the continuous two-sided stopped reward under a second-moment condition q < ψ(θ), with no separately postulated measurability of the limiting stopped payoff. This includes sample paths exiting precisely at the horizon. The stopped limit is integrable as part of the conclusion.
-- source:
--   Combine the accepted finite-horizon expectation convergence with the independent theorem proving the limiting reward's a.e. strong measurability by taking an a.e. limit of measurable clipped-grid stopped rewards.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_limit_aestrongly_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_expectation_tendsto
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_actual_ceiling_capped_grid_expectation_tendsto_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (lower upper : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    Integrable (fun ω =>
      Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
        W (x + X.X (min (τ ω) T) ω)) P ∧
    Tendsto (fun n => ∫ ω,
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω) ∂P)
      atTop (𝓝 (∫ ω,
        Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
          W (x + X.X (min (τ ω) T) ω) ∂P)) := by
  sorry
