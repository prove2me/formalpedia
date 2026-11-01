-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_count_locally_finite_all_borel_ae
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_count_locally_finite_all_borel_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:58:56.417531+00:00
-- url     : https://prove2.me/theorems/6e608416-1034-40ed-9ab6-f0035d8c76a5
-- title:
--   One full-measure event gives finite genuine source BV Lévy jump-count mass on every time and Borel mark rectangle
-- statement:
--   For the actual original-space bounded-variation spectrally negative Lévy process X of finite negative Lévy intensity, there exists one P-full event on which its intrinsic jump counting measure assigns finite mass to every rectangle (0,T]×B for every nonnegative finite horizon T and every Borel set B, simultaneously. No mark band separation or equal-law Poisson replacement is needed. This is the true source-X locally finite random counting measure's pathwise finiteness property, not an asserted measurable-kernel, Poisson or compensator law.
-- source:
--   Canonically Proved source-X simultaneous finite jump times e35efd8b-dffe-441a-8742-4aedd214f484 plus canonically Proved source intrinsic rectangular evaluation f6336d40-2d19-444f-bacd-83724316de67. For a fixed ω in the single full event, every mark-restricted original jump time set is a subset of the finite unmarked jump time set. Its extended cardinal is finite. Both quantifiers T and B remain inside the same almost-sure event.

import Mathlib.Data.Set.Card
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_count_locally_finite_all_borel_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ B : Set ℝ, MeasurableSet B →
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) < ⊤ := by sorry
