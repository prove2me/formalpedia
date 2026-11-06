-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_truncated_compensation_taylor_joint_predictable_mark_measurable
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_truncated_compensation_taylor_joint_predictable_mark_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:26:24.858018+00:00
-- url     : https://prove2.me/theorems/874d199f-3507-43b1-a1b7-6a10ac27b6bd
-- title:
--   Actual original state-dependent truncated-compensation Lévy Taylor kernel jointly predictable and mark measurable
-- statement:
--   The exact genuine original Lévy jump Taylor generator kernel with derivative compensation only for real marks z greater than -1 is jointly measurable in the original right-continuous predictable time-path sigma-algebra and real Borel Lévy marks. It uses the same controlled pre-jump reserve X-D, retaining the physical -1 Lévy truncation rather than compensating all large negative marks.
-- source:
--   Original physical controlled reserve predictable measurability 94ee9994; combine the genuine real mark projection and measurable derivative, and the original Lévy cutoff event {-1<z} in the product sigma-algebra using Measurable.ite. This corrects the full-z Taylor polynomial into the actual truncated Lévy generator kernel, without assuming finite large-jump second moments.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_truncated_compensation_taylor_joint_predictable_mark_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        (fun y : ℝ => w (y + p.2) - w y -
          (if -1 < p.2 then p.2 * deriv w y else 0))
          (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) := by sorry
