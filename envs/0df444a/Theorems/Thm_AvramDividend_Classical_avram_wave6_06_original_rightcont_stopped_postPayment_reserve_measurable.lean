-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
-- name    : AvramDividend.Classical.avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:11:11.713077+00:00
-- url     : https://prove2.me/theorems/4238f416-932d-46af-8bf9-0e10eacce32b
-- title:
--   Measurable original post-payment reserve at a genuine right-continuous stopping time
-- statement:
--   For actual original Levy X and original adapted left-continuous dividend D, evaluate U+_tau=x+X_tau-D_tau+ at arbitrary genuine right-continuous filtration stopping time tau. It is measurable without an independent terminal random-variable premise. Apply Proved joint measurability of right-continuous adapted post-payment reserve, Proved fixed-time X/rightLimit D measurability and hTau measurable. No Ito identity or ruin assumption.
-- source:
--   Original Avram Proposition 4(i), terminal pre-ruin branch, Eq (5.11)-(5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable (fun ω => x + X.X (τ ω) ω - rightLimit D (τ ω) ω) := by sorry
