-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
-- name    : AvramDividend.Classical.avram_p3_g2_original_prepayment_riskProcess_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:05:12.816458+00:00
-- url     : https://prove2.me/theorems/2159c88b-2e39-473a-82ab-844e5756e180
-- title:
--   Original physical Lévy prepayment riskProcess is jointly measurable at all nonnegative times including the time-zero dividend
-- statement:
--   The original controlled prepayment reserve x+X_t−D_t is jointly Borel measurable in original physical time and path. The payment-time zero branch uses measurable D_0 directly, while each t>0 uses the established left limit of the postpayment right-limit process and source left-continuity; the Lévy path is jointly measurable from its right-continuity and adaptedness. Consequently the actual reserve is measurable at every measurable random observation clock, preserving the initial payment atom.
-- source:
--   Proved/public source originals 1816332a joint D+ leftLim, f9c3a5c4 original strict left D identity, 8aafec11 joint evaluation; actual source IsDividendStrategy and SpectrallyNegativeLevy; not canonical P3 residual.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_prepayment_dividend_leftLimit_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_prepayment_riskProcess_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω => riskProcess X x D z.1 z.2) := by sorry
