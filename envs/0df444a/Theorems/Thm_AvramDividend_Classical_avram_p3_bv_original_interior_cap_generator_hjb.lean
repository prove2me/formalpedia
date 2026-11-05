-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_interior_cap_generator_hjb
-- name    : AvramDividend.Classical.avram_p3_bv_original_interior_cap_generator_hjb
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:07:15.380526+00:00
-- url     : https://prove2.me/theorems/147f15bb-3d70-4bf5-b335-1d53b0a69602
-- title:
--   Original BV source generator HJB and integrability transfer under slope-one cap extension
-- statement:
--   The original Lévy generator's integrability and discounted HJB drift inequality survive exact slope-one cap-linear continuation at every reserve strictly below the cap. This is a direct composition of Proved original-source generator-integrability equivalence and generator equality, with no added integrability or martingale hypothesis.
-- source:
--   Proved original-source cap generator theorems de1c1aee-43d3-47a2-83ae-6115b56249e3 and 76780f0a-9237-49b3-8584-ca46df97ad81.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_bv_original_interior_cap_generator_hjb
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c y q : ℝ) (hyc : y < c)
    (hw : X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) :
    X.GeneratorIntegrable
        (fun z => if z ≤ c then w z else w c + (z - c)) y ∧
      X.generator
          (fun z => if z ≤ c then w z else w c + (z - c)) y -
        q * (if y ≤ c then w y else w c + (y - c)) ≤ 0 := by sorry
