-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a368_ae_masked_finite_Young_energy_cross_budget
-- name    : AvramDividend.Classical.avram_ga_a368_ae_masked_finite_Young_energy_cross_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:12:33.897696+00:00
-- url     : https://prove2.me/theorems/84807369-fb6f-4fac-931b-c6ec4102f64e
-- title:
--   Gaussian full masked finite combined small-cell Young energy bound from a.e. Taylor, Lipschitz and Hessian source controls
-- statement:
--   For each physical finite mesh, if the original full stopping-cell source has pointwise nonnegative cell times, an almost-everywhere uniform one-sided Taylor remainder inequality, an almost-everywhere uniform local value-increment Lipschitz bound, and an almost-everywhere uniform Hessian bound, then almost every sample path satisfies the precise finite small-cell combined positive energy, cross and discount Young budget from the proved a290 theorem. The statement preserves a.e. qualifiers of source a194/a165 and is needed to derive a361 from a364.
-- source:
--   Original Gaussian a194,a165,a204 via proved finite small Young source theorem a290

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a290_original_masked_finite_combined_small_discount_Young_energy_budget
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a368_ae_masked_finite_Young_energy_cross_budget
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (s u v d h r z : ℕ → Ω → ℝ)
    (q Δ ε L M η : ℝ)
    (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hη : 0 < η)
    (hTime : ∀ i ω, A i ω → 0 ≤ s i ω)
    (hTaylor : ∀ᵐ ω ∂P, ∀ i, A i ω →
      max (Real.exp (-(q*s i ω)) *
        (v i ω-u i ω-d i ω*r i ω-h i ω/2*(r i ω)^2)) 0 ≤
        ε*(r i ω)^2)
    (hLip : ∀ᵐ ω ∂P, ∀ i, A i ω →
      |v i ω-u i ω| ≤ L*|r i ω|)
    (hHess : ∀ᵐ ω ∂P, ∀ i, A i ω →
      |h i ω| ≤ M) :
    ∀ᵐ ω ∂P,
      max (∑ i ∈ S, if A i ω then
        Real.exp (-(q*(s i ω+Δ)))*(v i ω-u i ω) -
          Real.exp (-(q*s i ω))*(d i ω*r i ω+h i ω/2*(z i ω)^2)
        else 0) 0 ≤
      ∑ i ∈ S, if A i ω then
        (ε+η)*(r i ω)^2+(q*Δ*L)^2/(4*η) +
          M/2*|(r i ω)^2-(z i ω)^2| else 0 := by sorry
