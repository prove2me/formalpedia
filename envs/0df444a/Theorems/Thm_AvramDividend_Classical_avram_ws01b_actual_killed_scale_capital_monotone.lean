-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_killed_scale_capital_monotone
-- name    : AvramDividend.Classical.avram_ws01b_actual_killed_scale_capital_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:00:51.113324+00:00
-- url     : https://prove2.me/theorems/48e1f66d-923e-4698-985e-02d0195261f3
-- title:
--   Actual original Lévy closed-window killed q-scale expectation is monotone in initial capital
-- statement:
--   For the actual spectrally negative Lévy process and any q-scale function W, increasing the initial reserve cannot decrease the closed-horizon discounted killed nonnegative expectation. This source-specific result includes reserve zero, needs no W(0)=0 assumption, and supplies Borel measurability of the capital kernel in the all-rate BV killed-semigroup proof.
-- source:
--   Actual source-path event inclusion under x≤y and canonically Proved global monotonicity of the true q-scale W, UUID 1c7655dc. Essential to BV killed q-scale semigroup good-time uniformisation without time regularity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01b_actual_killed_scale_capital_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (t : ℝ≥0) (x y : ℝ) (hxy : x ≤ y) :
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω))
      else (0 : ℝ≥0∞) ∂P) ≤
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ t → 0 ≤ y + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
          W (y + X.X t ω))
      else (0 : ℝ≥0∞) ∂P) := by sorry
