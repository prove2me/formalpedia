-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
-- name    : AvramDividend.Classical.avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:48:42.410195+00:00
-- url     : https://prove2.me/theorems/c8f49b8a-b0ad-4ef0-9808-f2f1d426fcb0
-- title:
--   Original physical stopped finite-grid discounted generator Riemann term Q is nonpositive
-- statement:
--   Under the pointwise super-generator HJB inequality, the actual original stopped physical-grid discounted left-point generator sum Q_j is nonpositive on every sample path and every finite mesh. Each term is a nonnegative discount and NNReal mesh step multiplied by a nonpositive generator/HJB residual, even for a nonmonotone input grid. This finite-grid sign permits expected-budget arguments without requiring pointwise convergence of generator Riemann sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (j : ℕ) (ω : Ω) :
    let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    (∑ i ∈ Finset.range (m j),
      E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
        (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
          X.generator w (Y (v i)) - q * w (Y (v i))
         else 0)) ≤ 0 := by sorry
