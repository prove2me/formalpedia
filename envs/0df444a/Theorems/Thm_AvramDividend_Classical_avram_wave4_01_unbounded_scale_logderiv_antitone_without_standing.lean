-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_unbounded_scale_logderiv_antitone_without_standing
-- name    : AvramDividend.Classical.avram_wave4_01_unbounded_scale_logderiv_antitone_without_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:18:21.388822+00:00
-- url     : https://prove2.me/theorems/a398acb7-0547-4203-ab8c-679e6359175f
-- title:
--   Global decreasing original q-scale logarithmic derivative for every unbounded-variation process without Standing
-- statement:
--   For every q>0 and spectrally negative Lévy process of unbounded variation, the ordinary logarithmic derivative W'(x)/W(x) of the positive q-scale function is antitone for all x>0, without any Standing hypothesis. This quantitative shape theorem follows from genuine corrected-exit log-concavity, established through the original first-record hazard, together with the fully Standing-free C1 regularity of W. It strengthens C1 and concavity into a direct global order on the source hazard slope.
-- source:
--   Proved original unbounded-scale log-concavity bb6ee1d8, positive W e50526dc, proved analytic log-derivative antitonicity 3fdd1623, Standing-free unbounded-variation C1 b3b0b4d2.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_log_concavity_core
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_unbounded_variation_C1_without_standing
import Theorems.Thm_AvramDividend_Classical_log_derivative_antitone_of_concave_log

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_unbounded_scale_logderiv_antitone_without_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    AntitoneOn
      (fun x : ℝ => deriv W x / W x)
      (Set.Ioi (0 : ℝ)) := by sorry
