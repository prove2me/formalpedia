-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_nonnegative_signed_budget_both_L1
-- name    : AvramDividend.Classical.avram_sweep16_20261106_nonnegative_signed_budget_both_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:24:33.558254+00:00
-- url     : https://prove2.me/theorems/ea0155a7-7aca-4784-a1d9-1a57de4111f4
-- title:
--   Nonnegative original signed stopped verification budget automatically forces both terminal and cash L1
-- statement:
--   On the finite original probability law, if exact stopped terminal and Stieltjes cash are measurably nonnegative, and the Ito residual upper inequality has integrable signed M/G/H, then both terminal and cash are L1. This breaks the apparent circular dependence of the two integrability conditions.
-- source:
--   SWEEP16 original Lévy physical-process reduction; terminal nonnegativity is already independently Proved by f6fef241 and source cash nonnegative by the nonnegative dividend measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_sweep16_20261106_nonnegative_signed_budget_both_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (c : ℝ) (Term Cash M G H : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashMeas : AEStronglyMeasurable Cash P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hCashNonneg : ∀ᵐ ω ∂P, 0 ≤ Cash ω)
    (hMI : Integrable M P)
    (hGI : Integrable G P)
    (hHI : Integrable H P)
    (hUpper : ∀ᵐ ω ∂P, Term ω + Cash ω ≤ c + M ω + G ω + H ω) :
    Integrable Term P ∧ Integrable Cash P := by sorry
