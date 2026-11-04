-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_integrable_centered_jump_plus_HJB_cash_nonpos
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_integrable_centered_jump_plus_HJB_cash_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:28:35.233699+00:00
-- url     : https://prove2.me/theorems/5975ece6-6639-4940-9a52-55d20365ec60
-- title:
--   Integrable original stopped centred-jump plus HJB drift expected cash bound
-- statement:
--   Conditional measure-theoretic assembly over the same original probability measure P: an integrable centred source jump compensation M with expected value zero and an independently integrable original HJB drift B with nonpositive mean combine into an integrable signed cash budget with nonpositive expectation. This theorem introduces no compensator axiom and makes no claim about the availability of hM or hB. Those source-specific obligations must be discharged by the separately proved P3-B original-process helpers.
-- source:
--   Mathlib MeasureTheory.Integrable.add and integral_add

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_integrable_centered_jump_plus_HJB_cash_nonpos{Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M B : Ω → ℝ)
    (hM : Integrable M P ∧ (∫ ω, M ω ∂P) = 0)
    (hB : Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) :
    Integrable (fun ω => M ω + B ω) P ∧
      (∫ ω, M ω + B ω ∂P) ≤ 0 := by sorry
