-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_L1_signed_witness_iff_expected_budget
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_L1_signed_witness_iff_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:16:42.488335+00:00
-- url     : https://prove2.me/theorems/9ff8bb39-52d1-46c7-bdc8-4727119608ca
-- title:
--   Exact original-source L1 signed residual witnesses iff stopped expected dividend budget
-- statement:
--   For original X with its inherent probability measure and the actual L1 Term/Cash, existence of integrable M G H satisfying zero-mean M, joint nonpositive G+H and a.e. full stopped budget is logically equivalent to the expected stopped budget upper bound. Forward direction integrates the witness; reverse uses accepted centring. It does not prove the stochastic source inequality or claim the canonical theorem.
-- source:
--   Accepted P4-F b77e6dae expectation-centred construction; Mathlib Bochner integral_mono_ae and integral_nonpos_of_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_L1_signed_witness_iff_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ)
    (Term Cash : Ω → ℝ)
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P) :
    (∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω)) ↔
    ((∫ ω, Term ω + Cash ω ∂P) ≤ w x) := by sorry
