-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_all_nonnegative_borel_mark_predictable_rectangle_zero
-- name    : AvramDividend.Classical.avram_wave7_01_original_all_nonnegative_borel_mark_predictable_rectangle_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:26:36.833115+00:00
-- url     : https://prove2.me/theorems/fb9249b4-278e-485b-87f5-92613fec83e7
-- title:
--   Original predictable rectangle compensator is exactly zero for every nonnegative-supported Borel mark set
-- statement:
--   For the unchanged SpectrallyNegativeLevy P 𝓕 and any Borel mark set B contained in [0,∞), the literal original source intrinsic marked count on (s,t]×B is zero on every source sample, and ν(B)=0. Thus the exact predictable original-past rectangle identity holds without BV, finite activity or a hypothetical extractor.
-- source:
--   Proved actual original pathwise global nonnegative jump-mark mass zero 0a9afdb9-4d96-45fb-998e-d7a78f798a44; source spectral negativity ν_Ici=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_all_nonnegative_borel_mark_predictable_rectangle_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNonneg : B ⊆ Ici (0 : ℝ)) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
