-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a325_nonnegative_measurable_Gaussian_source_integrable_two_positive_tail_majorant
-- name    : AvramDividend.Classical.avram_ga_a325_nonnegative_measurable_Gaussian_source_integrable_two_positive_tail_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:00:17.395566+00:00
-- url     : https://prove2.me/theorems/15ca450e-3c28-49a2-b284-525f3e639883
-- title:
--   A.e. strongly measurable nonnegative Gaussian source dominated by two integrable nonnegative rare-event tails is integrable
-- statement:
--   A nonnegative almost-everywhere strongly measurable source F under a probability law is Bochner integrable whenever it is almost surely dominated by a nonnegative linear combination of two nonnegative integrable tail sources S and Q. This is the exact analytic domination needed for original a263 large fully stopped Gaussian positive source from the a319 true HJB signed/rare polynomial upper bound, a320 original signed/polynomial integrability and a323 true rare combined measurability.
-- source:
--   Mathlib Integrable.mono and Bochner finite linear combinations; original Gaussian source a319/a320/a323.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a325_nonnegative_measurable_Gaussian_source_integrable_two_positive_tail_majorant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F S Q : Ω → ℝ) (c d : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hFm : AEStronglyMeasurable F P)
    (hSI : Integrable S P) (hQI : Integrable Q P)
    (hFpos : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hSpos : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (hQpos : ∀ᵐ ω ∂P, 0 ≤ Q ω)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ c*S ω + d*Q ω) :
    Integrable F P := by sorry
