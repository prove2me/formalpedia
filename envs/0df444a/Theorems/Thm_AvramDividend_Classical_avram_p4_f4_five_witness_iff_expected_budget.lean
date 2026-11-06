-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_five_witness_iff_expected_budget
-- name    : AvramDividend.Classical.avram_p4_f4_five_witness_iff_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:52:11.260959+00:00
-- url     : https://prove2.me/theorems/388d9c1a-4d92-4f01-ad9d-9bd28ffe8689
-- title:
--   Exact five-component stopped source witness existence iff integrable expected-value budget
-- statement:
--   For integrable original stopped terminal and dividend cash at a probability measure, existence of the five literal residual functions with integrable and centred Mc/Ms/Ml, integrable nonpositive G, nonpositive R and the upper pathwise reward inequality is equivalent to the expected reward budget. The forward direction centres the actual stopped reward. The reverse direction takes expectations after removing nonpositive residuals. The theorem does not claim its centred witness equals an Ito-Meyer source martingale and does not assume the independent budget for the canonical target.
-- source:
--   Exact logical characterization of fdb9a6a3's existential conclusion under independently established Term integrability, with zero Gaussian/jump semantic attribution. It isolates the genuine missing natural-clock expected budget and offers a precise parent application without importing downstream P4-F sources.

import Mathlib

open MeasureTheory

noncomputable section

/-- The five residual slots at an original stopped clock are equivalent
to its expected payoff budget once terminal and cash integrability hold. -/

theorem AvramDividend.Classical.avram_p4_f4_five_witness_iff_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Term Cash : Ω → ℝ) (hTerm : Integrable Term P)
    (hCash : Integrable Cash P) (b : ℝ) :
    (∫ ω, Term ω + Cash ω ∂P) ≤ b ↔
      ∃ Mc Ms Ml G R : Ω → ℝ,
        Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
        Integrable G P ∧
        (∫ ω, Mc ω ∂P) = 0 ∧
        (∫ ω, Ms ω ∂P) = 0 ∧
        (∫ ω, Ml ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, G ω ≤ 0) ∧
        (∀ᵐ ω ∂P, R ω ≤ 0) ∧
        (∀ᵐ ω ∂P, Term ω + Cash ω ≤
          b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
