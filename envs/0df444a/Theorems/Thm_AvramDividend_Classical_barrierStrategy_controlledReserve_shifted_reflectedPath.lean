-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_controlledReserve_shifted_reflectedPath
-- name    : AvramDividend.Classical.barrierStrategy_controlledReserve_shifted_reflectedPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:34:00.960713+00:00
-- url     : https://prove2.me/theorems/26a85d1c-526e-41c5-9d8a-e54d2dd1454a
-- title:
--   Post-upcrossing controlled reserve is the reflected shifted Lévy increment path
-- statement:
--   At the first finite upward crossing u of a-x, after any elapsed time t the controlled surplus under the barrier strategy equals the reserve a plus the increment after u minus the running maximum of the shifted Lévy increments. The formula identifies the exact future ruin event and is essential for translating killed dividend-payment windows.
-- source:
--   Direct child 79978d61-9d1f-4b20-b8a5-114797a8e380. Uses proved finite first crossing attainment, zero dividend at crossing, shifted running-supremum dividend increment and boundedness. The conclusion specifies post-crossing ruin in terms of shifted path, without W/scale parameters.

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_at_firstUpcrossing_zero
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_increment_eq_shiftedSup
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierStrategy_controlledReserve_shifted_reflectedPath
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    riskProcess X x (barrierStrategy X x a) (u + t) ω =
      a + (X.X (u + t) ω - X.X u ω) -
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) ''
          Set.Icc 0 t) := by
  sorry
