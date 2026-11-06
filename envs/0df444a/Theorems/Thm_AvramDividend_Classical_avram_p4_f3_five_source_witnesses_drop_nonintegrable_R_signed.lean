-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_five_source_witnesses_drop_nonintegrable_R_signed
-- name    : AvramDividend.Classical.avram_p4_f3_five_source_witnesses_drop_nonintegrable_R_signed
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:40:47.186107+00:00
-- url     : https://prove2.me/theorems/ac622130-2c96-4571-b488-f6aae75ecd68
-- title:
--   Five original physical Itô witnesses imply signed UBV witnesses without integrability of the residual
-- statement:
--   Take the three centred integrable original stopped Gaussian, small-jump and large-jump martingales and sum them into one integrable mean-zero witness. Keep the original nonpositive integrable generator term and set the third signed witness to zero. The potentially nonintegrable nonpositive residual R can be discarded pointwise. This is a rigorous acyclic bridge from the original source-components theorem to the signed residual theorem.
-- source:
--   Formal regrouping of integrable original stopped residuals. In particular the original R is not assumed integrable; no independence or equality-in-law premise is introduced.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_p4_f3_five_source_witnesses_drop_nonintegrable_R_signed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Term Cash : Ω → ℝ) (b : ℝ)
    (hSource : ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        b + Mc ω + Ms ω + Ml ω + G ω + R ω)) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ b + M ω + G ω + H ω) := by sorry
