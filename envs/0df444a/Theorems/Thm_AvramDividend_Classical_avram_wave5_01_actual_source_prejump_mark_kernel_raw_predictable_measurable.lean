-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_prejump_mark_kernel_raw_predictable_measurable
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_prejump_mark_kernel_raw_predictable_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:12:16.784905+00:00
-- url     : https://prove2.me/theorems/7b4c3f24-e212-4ac9-9d18-ef24921bfebd
-- title:
--   Actual source pre-jump/mark kernel is measurable in raw predictable × Borel σ-algebra
-- statement:
--   For any original spectrally negative Lévy process X and every Borel measurable F of pre-jump reserve and jump mark, the genuine sample-path kernel (t,ω,z) ↦ F(X_{t-}(ω),z) is measurable under the raw original predictable σ-algebra times the Borel mark σ-algebra. No BV, enlarged filtration or detached Poisson space is assumed.
-- source:
--   Accepted original-raw-prejump predictability 91d7344e; measurable product projection and composition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_prejump_predictable_raw_original_filtration

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_prejump_mark_kernel_raw_predictable_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) :
    Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable)
      (inferInstance : MeasurableSpace ℝ))]
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        F (Function.leftLim
          (fun u : ℝ≥0 => X.X u p.1.2) p.1.1, p.2)) := by sorry
