-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_conditional_upper_to_exact_centered_martingale_budget
-- name    : AvramDividend.Classical.avram_jump6_A_conditional_upper_to_exact_centered_martingale_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:25:43.588265+00:00
-- url     : https://prove2.me/theorems/77a8b5d0-53ec-437e-a257-6db12d648196
-- title:
--   Conditional expected reward budget yields exact centred signed pathwise martingale witness
-- statement:
--   For an integrable payoff F on the original filtered probability space, if its conditional expectation given the initial history is bounded above by the proposed HJB value b, then construct the genuine integrable centred surprise martingale MG=F−E[F|H], the zero MJ channel, and nonpositive signed drift B=E[F|H]−b. The pathwise ledger is an exact identity, and both initial conditional expectations vanish. This is a reusable mathematically correct alternative to Gaussian-plus-smallmark linear mesh sources that omit nonlinear compensated full negative marks. It does not assert the original conditional HJB budget without proof.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_conditional_upper_to_exact_centered_martingale_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℋ : MeasurableSpace Ω) (hℋ : ℋ ≤ mΩ)
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ)
    (hUpper : ∀ᵐ ω ∂P, P[F | ℋ] ω ≤ b) :
    ∃ MG MJ B : Ω → ℝ,
      Integrable MG P ∧ Integrable MJ P ∧
      P[MG | ℋ] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      P[MJ | ℋ] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
      (∀ᵐ ω ∂P, B ω ≤ 0) ∧
      (∀ ω, F ω = b + MG ω + MJ ω + B ω) := by sorry
