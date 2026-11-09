-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_0b16_nonnegative_payoff_certificate_forces_integrable_negative_source
-- name    : AvramDividend.Classical.avram_0b16_nonnegative_payoff_certificate_forces_integrable_negative_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T09:36:24.262983+00:00
-- url     : https://prove2.me/theorems/2dff4def-4d3c-4675-b4fa-cbaebc52ab34
-- title:
--   Nonnegative physical payoffs force integrability of a negative source budget under L1 martingale and error
-- statement:
--   A source-exact obstruction to BV stopped physical budget certificates: on a finite measure space, if the payout is almost everywhere nonnegative, the negative original generator source is almost everywhere strongly measurable and nonpositive, and the physical payoff is bounded above by a constant plus integrable martingale and error plus the source, then the source must be integrable. This requires no integrability hypothesis on the payout. It diagnoses the attempt to establish the original no-source-L1 pathwise inequality before discarding the generator term in Avram theorem 07d7e4be and 88ba7839.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_0b16_nonnegative_payoff_certificate_forces_integrable_negative_source
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F M B Err : Ω → ℝ) (a : ℝ)
    (hF : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hM : Integrable M P) (hErr : Integrable Err P)
    (hBmeas : AEStronglyMeasurable B P)
    (hBneg : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hPath : ∀ᵐ ω ∂P,
      F ω ≤ a + (M ω + B ω) + Err ω) :
    Integrable B P := by sorry
