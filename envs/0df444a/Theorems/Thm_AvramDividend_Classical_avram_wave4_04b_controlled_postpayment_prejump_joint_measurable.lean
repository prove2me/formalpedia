-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
-- name    : AvramDividend.Classical.avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:15:28.824689+00:00
-- url     : https://prove2.me/theorems/d1627b7b-f087-4a3a-aea8-a13cebc3e57d
-- title:
--   Actual controlled reserve strict-left-limit jointly measurable in original time and probability
-- statement:
--   For actual spectrally negative Lévy X and an arbitrary same-filtration adapted dividend strategy with right jumps and singular continuous variation, the strict pre-jump left limit of the postpayment reserve U⁺ is jointly Borel measurable in nonnegative time and original sample point. The time-zero value is the exact Mathlib Function.leftLim, not a silently substituted state. This supplies the actual U⁺_{t-} evaluation needed by the source compensated generator and complete continuous Stieltjes correction.
-- source:
--   Proved postPaymentReserve_cadlag_adapted and stronglyAdapted_leftLim_of_exists_leftLimits plus right-continuous measurable sections; adapt the verified actual Lévy pre-jump dyadic-from-below proof, preserving the original dividend strategy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s z.2 - rightLimit D s z.2)
        z.1) := by
  sorry
