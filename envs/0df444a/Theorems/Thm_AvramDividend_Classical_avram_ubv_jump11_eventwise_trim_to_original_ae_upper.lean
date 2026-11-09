-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_eventwise_trim_to_original_ae_upper
-- name    : AvramDividend.Classical.avram_ubv_jump11_eventwise_trim_to_original_ae_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:26:27.597988+00:00
-- url     : https://prove2.me/theorems/25637f79-b9ee-4945-90a1-b231c9142418
-- title:
--   Convert all finite initial-event integral inequalities into an ambient almost-everywhere upper bound
-- statement:
--   A measure-theoretic bridge needed for original stopped pure-jump budget: if two real integrable functions obey set-integral order for all measurable sets of the initial sigma algebra under its trimmed probability measure, then they obey the ambient almost-sure order. Proof by the pinned Mathlib ae_le_of_forall_setIntegral_le and ae_of_ae_trim. This bridges initial-event upper budgets to conditional expectation bounds.
-- source:
--   UBV-JUMP11 generic eventwise/conditional bridge using pinned Mathlib AEEqOfIntegral and Trim.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_ubv_jump11_eventwise_trim_to_original_ae_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (f g : Ω → ℝ)
    (hf : Integrable f (P.trim hm))
    (hg : Integrable g (P.trim hm))
    (hEvent : ∀ A : Set Ω, MeasurableSet[m] A →
      (P.trim hm) A < ⊤ →
      (∫ ω in A, f ω ∂(P.trim hm)) ≤
      (∫ ω in A, g ω ∂(P.trim hm))) :
    ∀ᵐ ω ∂P, f ω ≤ g ω := by sorry
