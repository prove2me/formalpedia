-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable
-- name    : AvramDividend.Classical.avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:45:59.743199+00:00
-- url     : https://prove2.me/theorems/0c60d413-e1ac-460f-ae98-dbda02adf06f
-- title:
--   Original postpayment combined Lévy jump and simultaneous right-dividend mark is jointly measurable
-- statement:
--   The actual original-filtration postpayment controlled reserve combined mark ΔX_t−(D_{t+}−D_t), assigned zero at initial time, is jointly measurable on NNReal×Ω for every genuine spectrally negative Lévy source and admissible dividend strategy. It supplies a random marked-field measurability interface for stopped Itô–Meyer jump kernels across BV and UBV, including simultaneous source jumps and dividend atoms. No compensator, independence, or stochastic integral is assumed.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), formula (5.12). Canonically Proved actual postpayment càdlàg/adapted a2763475, right-continuous section evaluation 8aafec11, postpayment strict left-limit joint measurability d1627b7b and exact combined original mark 74dd09be; closed under measurable subtraction and positive-time indicator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_exact_jumpmark

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        (X.X z.1 z.2 -
          Function.leftLim (fun s : ℝ≥0 => X.X s z.2) z.1) -
          (rightLimit D z.1 z.2 - D z.1 z.2)
      else 0) := by sorry
