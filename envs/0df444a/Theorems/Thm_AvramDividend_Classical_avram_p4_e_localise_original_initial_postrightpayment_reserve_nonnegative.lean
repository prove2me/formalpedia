-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postrightpayment_reserve_nonnegative
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_initial_postrightpayment_reserve_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:44:42.91041+00:00
-- url     : https://prove2.me/theorems/bcb48566-c0e4-48d2-8a5d-f765d99444e5
-- title:
--   Original admissible strategy cannot create a negative initial reserve by its time-zero right-payment atom
-- statement:
--   For the genuine original reserve and rightLimit D0, the source admissibility inequality at t=0 implies x+X.X0-rightLimit D0≥0. This establishes the correct side of the immediate terminal postpayment branch W at τ=0 without assuming boundary time occupation vanishes or changing the cash atom convention.
-- source:
--   Original IsAdmissible t=0 branch and riskProcess definition in DividendStrategy source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Admissibility at time zero protects the original terminal post-rightpayment reserve. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_initial_postrightpayment_reserve_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (ω : Ω) :
    0 ≤ x + X.X 0 ω - rightLimit D 0 ω := by sorry
