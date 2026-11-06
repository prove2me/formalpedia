-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_ubv_vcstar_zero_reserve
-- name    : AvramDividend.Classical.avram_sweep16_ubv_vcstar_zero_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:01:35.509237+00:00
-- url     : https://prove2.me/theorems/4866b3e7-c515-41d1-894d-4465eaa0dba2
-- title:
--   Unbounded-variation c-star verification candidate vanishes at zero initial reserve
-- statement:
--   Exact zero-reserve boundary identity of the original c-star
--   verification candidate under unbounded variation. The previously Proved
--   source theorem gives W(0)=0, and the original piecewise vcstar formula
--   agrees with the scaled W function at every real point not exceeding
--   cstar, in particular zero. Extended division by any finite derivative
--   preserves zero numerator. No smoothness, finite-cstar or Ito hypothesis.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_on_Iic_cstar

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_ubv_vcstar_zero_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    vcstar W 0 = 0 := by sorry
