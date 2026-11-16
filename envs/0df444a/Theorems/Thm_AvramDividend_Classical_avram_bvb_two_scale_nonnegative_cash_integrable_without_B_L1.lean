-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_two_scale_nonnegative_cash_integrable_without_B_L1
-- name    : AvramDividend.Classical.avram_bvb_two_scale_nonnegative_cash_integrable_without_B_L1
-- status  : Disproved
-- author  : @WillR
-- created : 2026-11-15T11:25:48.380696+00:00
-- url     : https://prove2.me/theorems/ee6847b0-fe8e-4461-997c-008d26005ae9
-- title:
--   The original nonnegative two-scale stopped cash is automatically L1 under centred integrable noise and positive error envelope, with no B integrability assumption
-- statement:
--   Given a.e. measurable nonnegative stopped dividend cash F, its pointwise two-scale upper budget by a real initial candidate, an L1 noise M, a nonpositive potentially nonintegrable physical generator grid B, and two L1 positive error channels, the cash F itself is automatically integrable. No moment or integrability assumption on B is introduced. Combined with the companion expected-bound theorem this yields the original BV B upper verification after removal of B.
-- source:
--   Drop nonpositive B, bound the constant and M by absolute values, form a finite integrable positive envelope and apply the pinned integrable mono nonnegative theorem.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_bvb_two_scale_nonnegative_cash_integrable_without_B_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (a : ℝ) (F M B E₁ E₂ : Ω → ℝ)
    (hFmeas : AEStronglyMeasurable F P)
    (hFnonneg : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hM : Integrable M P)
    (hE₁ : Integrable (fun ω => max (E₁ ω) 0) P)
    (hE₂ : Integrable (fun ω => max (E₂ ω) 0) P)
    (hB : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ a + M ω + B ω + max (E₁ ω) 0 + max (E₂ ω) 0) :
    Integrable F P := by sorry
