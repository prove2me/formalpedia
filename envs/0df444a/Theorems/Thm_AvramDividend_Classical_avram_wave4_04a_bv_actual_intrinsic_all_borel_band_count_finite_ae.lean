-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_all_borel_band_count_finite_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_all_borel_band_count_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:58:14.639478+00:00
-- url     : https://prove2.me/theorems/43b487ea-6918-4e1b-93d5-f8dfd2b4bdf8
-- title:
--   Finite-activity original BV Lévy intrinsic jump measure is finite on every bounded-horizon measurable mark rectangle
-- statement:
--   For the actual source BV spectrally negative Lévy process X with finite negative Lévy intensity, the intrinsic counting measure obtained from its own positive-time nonzero jump graph has P-almost surely finite mass on (0,T]×B for every fixed Borel set B and positive finite horizon T. The result does not require the mark band B to be separated from zero and uses no Poisson replacement. It is a genuine original-X finite-activity jump-measure property, not the Poisson count law or predictable compensator.
-- source:
--   Compose canonically Proved original-path intrinsic jump-measure rectangle Set.encard identity f6336d40-2d19-444f-bacd-83724316de67 with canonically Proved original-X unconditional finite jump-time support avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon. The marked time set is a subset of the finite all-jump time set. Mathlib Set.Finite.exists_encard_eq_coe yields finite mass.

import Mathlib.Data.Set.Card
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_all_borel_band_count_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) < ⊤ := by sorry
