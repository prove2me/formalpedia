-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_global_continuous_of_zero_scale_origin
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_global_continuous_of_zero_scale_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:40:35.388783+00:00
-- url     : https://prove2.me/theorems/4dd886a2-396c-40f0-ab44-8f6d3948dd7d
-- title:
--   Global continuity of the positive optimal-barrier candidate when the scale function vanishes at reserve zero
-- statement:
--   The classical capped dividend value is continuous at every real reserve, including zero, when the genuine q-scale function vanishes at zero and the optimal cap is finite and strictly positive. Above zero its continuity is already a proved barrier regularity fact; below zero the actual source candidate is zero, and the scale-ratio identity makes its value at zero vanish. This is a necessary hypothesis for pointwise compensated generator-jump continuity, including any jump that lands exactly at the reserve origin.
-- source:
--   Avram, Palmowski and Pistorius (2007) barrier candidate piecewise formula (5.1); accepted vcstar_basic_boundary_regular_of_positive_cstar UUID c6167930 and vcstar_eq_scaledW_on_Iic_cstar UUID 29a56575. P3 residual continuity and endpoint HJB.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_global_continuous_of_zero_scale_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hzero : W 0 = 0) :
    Continuous (vcstar W) := by sorry
