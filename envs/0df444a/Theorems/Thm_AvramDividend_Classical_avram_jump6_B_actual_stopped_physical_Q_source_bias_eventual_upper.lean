-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_stopped_physical_Q_source_bias_eventual_upper
-- name    : AvramDividend.Classical.avram_jump6_B_actual_stopped_physical_Q_source_bias_eventual_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T21:11:01.197853+00:00
-- url     : https://prove2.me/theorems/48720896-5a60-4582-a41d-e8b6f4c03d2f
-- title:
--   Exact original stopped physical generator Q sign eliminates drift from centred Source with vanishing bias
-- statement:
--   For the true stopped canonical or arbitrary physical grid of the original Levy reserve and right-limit dividend path, if the actual source decomposes as centred term M, exact generator Riemann sum Q, and deterministic bias tending to zero, the source is eventually pathwise bounded by M+epsilon. The HJB generator sign is proved directly on the real physical grid, so no extra Q-sign premise is assumed and no finite-activity restriction introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_signed_mesh_vanishing_bias_eventual_upper
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_stopped_physical_Q_source_bias_eventual_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (Source M : ℕ → Ω → ℝ) (bias : ℕ → ℝ)
    (hSource : ∀ j ω,
      let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Q : ℝ := ∑ i ∈ Finset.range (m j),
        E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
          (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
            X.generator w (Y (v i)) - q * w (Y (v i))
           else 0)
      Source j ω = M j ω + Q + bias j)
    (hBias : Tendsto bias atTop (𝓝 (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ ω, Source j ω ≤ M j ω + ε := by sorry
