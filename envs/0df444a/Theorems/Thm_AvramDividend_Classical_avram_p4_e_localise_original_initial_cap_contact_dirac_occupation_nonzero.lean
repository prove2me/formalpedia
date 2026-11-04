-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_cap_contact_dirac_occupation_nonzero
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_initial_cap_contact_dirac_occupation_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:28:00.804502+00:00
-- url     : https://prove2.me/theorems/3ed5a410-1f21-4ba8-96cf-1fdc5a2a42d3
-- title:
--   Original admissible cap contact at t=0 can carry positive Dirac physical-time occupation
-- statement:
--   For the genuine original source reserve riskProcess X x D, on any path whose pre-rightpayment book reserve at time zero equals the finite real cap and whose ruin-dominated target clock is strictly positive, the cap-contact indicator has integral exactly one under the deterministic Dirac observation-time measure at zero. This is a pathwise conditional mathematical counterexample to eliminating the cap contact at time zero under arbitrary s-finite measures, explaining why the accepted original cap occupation theorem restricts to t>0. It does not assert that every admissible strategy starts at the cap or that Lebesgue time charges t=0.
-- source:
--   Original source riskProcess and ruin clock definitions; Mathlib lintegral_dirac. Independent proved original cap occupation cc500549-ba08-47b0-b5c0-07c7a9bb40f3 deliberately only covers positive times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_initial_cap_contact_dirac_occupation_nonzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0∞) (ω : Ω)
    (hτ0 : 0 < τ ω)
    (hCap0 : riskProcess X x D 0 ω = c) :
    (∫⁻ t : ℝ≥0,
      if (t : ℝ≥0∞) < τ ω ∧ riskProcess X x D t ω = c
      then (1 : ℝ≥0∞) else 0 ∂(Measure.dirac (0 : ℝ≥0))) = 1 := by sorry
