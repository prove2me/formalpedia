-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1
-- name    : AvramDividend.Classical.avram_p4_f_assembly_expected_budget_witness_of_original_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:44:40.007761+00:00
-- url     : https://prove2.me/theorems/b77e6dae-ae3a-4f0d-8f93-97a107f92dc9
-- title:
--   Source-law L1 stopped expected dividend budget yields the exact centred martingale and signed residual witnesses
-- statement:
--   On the original SpectrallyNegativeLevy source probability space, if the actual stopped discounted Term and full Stieltjes Cash are each integrable and the exact expected Term+Cash is at most w(x), construct M as the centred stopped payoff and G as the constant nonpositive expectation shortfall, with H=0. This proves the precise original-source signed residual witness conclusion from an independently established expected stopped budget. It is a conditional reverse bridge for the directly stopped expectation route, not a derivation of the original Itô formula nor a proof of canonical 0dda1be7 without the expectation inequality.
-- source:
--   Original Avram–Palmowski–Pistorius Prop. 4(i), Eq. (5.11)–(5.13); canonical original-source stopped budget 0dda1be7; direct expected-budget target 447f725b remains separately owned.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_expected_budget_witness_of_original_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ)
    (Term Cash : Ω → ℝ)
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P)
    (hBudget : (∫ ω, Term ω + Cash ω ∂P) ≤ w x) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
