-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b20_nostanding_finiteactivity_integer_negative_jumps_equal_drift_deficit
-- name    : AvramDividend.Classical.avram_b20_nostanding_finiteactivity_integer_negative_jumps_equal_drift_deficit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:21:00.670032+00:00
-- url     : https://prove2.me/theorems/f8714ea4-f049-417f-b972-f22e2ececf51
-- title:
--   Finite-activity original integer-horizon negative jumps equal physical drift deficit
-- statement:
--   Almost surely at every integer horizon, the actual nonnegative sum of downward jumps of the original BV Lévy sample path equals n times its BV drift minus the original Lévy surplus. This source identity retains the original sample path, event and summation definition, with no Standing assumption.
-- source:
--   Lévy-Itô finite variation decomposition; Avram-Palmowski-Pistorius (2007) original BV source

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b20_nostanding_finiteactivity_integer_negative_jumps_equal_drift_deficit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) = (n : ℝ) * X.drift - X.X (n : ℝ≥0) ω := by sorry
