-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_stopped_generator_Q_expected_nonpositive_any_measure
-- name    : AvramDividend.Classical.avram_jump6_B_original_stopped_generator_Q_expected_nonpositive_any_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T21:13:48.706823+00:00
-- url     : https://prove2.me/theorems/a764622d-eb74-44d5-8557-a597452beca8
-- title:
--   Original pathwise nonpositive physical HJB generator grid has nonpositive expectation under any finite-integrability measure
-- statement:
--   For the exact original stopped physical time-grid generator Riemann term Q_j on the Levy reserve and original right-limit dividends, its expectation is nonpositive under any chosen measure when Q_j is integrable. In particular one may take the probability restricted to the positive-clock event, without extra source idealisations or finite-activity assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_stopped_generator_Q_expected_nonpositive_any_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (μ : Measure Ω) (j : ℕ) :
    let Q : Ω → ℝ := fun ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      ∑ i ∈ Finset.range (m j),
        E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
          (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
            X.generator w (Y (v i)) - q * w (Y (v i))
           else 0)
    Integrable Q μ → (∫ ω, Q ω ∂μ) ≤ 0 := by sorry
