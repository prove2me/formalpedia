-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_prepayment_controlled_source_leftjump_joint_measurable
-- name    : AvramDividend.Classical.avram_wave4_p2_prepayment_controlled_source_leftjump_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:49:24.632525+00:00
-- url     : https://prove2.me/theorems/a8c504b9-b038-42a6-9f60-271142e3f136
-- title:
--   Original controlled pre-payment source left-jump mark is jointly measurable in time and sample
-- statement:
--   For the actual given original spectrally negative Lévy source, its original probability space and filtration, and any admissible left-continuous dividend strategy, the positive-time left-jump mark of the original pre-payment reserve riskProcess is jointly Borel measurable on nonnegative time×original Ω, with zero extension at t=0. This follows from the already proved joint measurability of the actual Lévy jump mark and the independently proved source identity Δ^-riskProcess=Δ^-X at t>0. It gives a useful source-jump integrand measurability interface for BV/UBV marked-jump Itô–Meyer calculations without replacing X by a model process or assuming a conditional Poisson compensator.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), original source jump terms. Accepted original-path mark measurability 9d68c5c2 and exact original pre-payment reserve mark d2800259.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_wave4_p2_prepayment_controlled_source_leftjump_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω =>
      if 0 < z.1 then
        riskProcess X x D z.1 z.2 -
          Function.leftLim
            (fun s : ℝ≥0 => riskProcess X x D s z.2) z.1
      else (0 : ℝ)) := by sorry
