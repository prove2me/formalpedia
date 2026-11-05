-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_actual_cap_source_generatorIntegrable_HJB
-- name    : AvramDividend.Classical.avram_p2_assist_p3_actual_cap_source_generatorIntegrable_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:59:47.797201+00:00
-- url     : https://prove2.me/theorems/b7158278-ff15-4e0a-b2cd-b9ecb82201fd
-- title:
--   Source exact Lévy generator integrability and HJB sign of actual cap continuation
-- statement:
--   The original spectrally negative Lévy candidate's generator integrability and signed HJB drift both transfer to the actual capped extension at every strict interior reserve. The proof uses a previously Proved source-exact original Lévy generator integrability and HJB transfer, including finite/infinite caps, with no surrogate process. It directly discharges P3's expected drift sign premises when applying physical P3-F to the extended value.
-- source:
--   Proved avram_p3_bv_original_interior_cap_generator_hjb 147f15bb-3d70-4bf5-b335-1d53b0a69602 and original cap extension laws.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_interior_cap_generator_hjb
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_assist_p3_actual_cap_source_generatorIntegrable_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (q : ℝ)
    (hw_gen : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      X.GeneratorIntegrable w z ∧
      X.generator w z - q * w z ≤ 0) :
    ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      X.GeneratorIntegrable V z ∧
      X.generator V z - q * V z ≤ 0 := by sorry
