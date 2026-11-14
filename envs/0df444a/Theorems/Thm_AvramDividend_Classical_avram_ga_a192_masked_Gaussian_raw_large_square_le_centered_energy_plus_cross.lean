-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a192_masked_Gaussian_raw_large_square_le_centered_energy_plus_cross
-- name    : AvramDividend.Classical.avram_ga_a192_masked_Gaussian_raw_large_square_le_centered_energy_plus_cross
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:04:28.098967+00:00
-- url     : https://prove2.me/theorems/bff242be-539f-4dca-902a-39cfef1a57e4
-- title:
--   Every finite masked Gaussian raw large-square tail is between zero and centred quadratic energy plus raw-centred cross
-- statement:
--   For an arbitrary finite measurable or nonmeasurable cell selection and real centred increments Z, the sum of squared raw increments Z+d restricted to a large-increment threshold is nonnegative and bounded by the masked centred squared energy plus the absolute raw-centred quadratic cross. This is the deterministic inequality required for integrability of the true stopped original Gaussian raw tail without extra probability assumptions.
-- source:
--   Elementary x²≤y²+|x²-y²| and finite masked sum monotonicity.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_ga_a192_masked_Gaussian_raw_large_square_le_centered_energy_plus_cross
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (Z : ℕ → Ω → ℝ) (d η : ℝ) (ω : Ω) :
    let Tail : ℝ := ∑ i ∈ S, if A i ω then
      (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0) else 0
    let Energy : ℝ := ∑ i ∈ S, if A i ω then (Z i ω)^2 else 0
    let Cross : ℝ := ∑ i ∈ S, if A i ω then
      |(Z i ω + d)^2 - (Z i ω)^2| else 0
    0 ≤ Tail ∧ Tail ≤ Energy + Cross := by sorry
