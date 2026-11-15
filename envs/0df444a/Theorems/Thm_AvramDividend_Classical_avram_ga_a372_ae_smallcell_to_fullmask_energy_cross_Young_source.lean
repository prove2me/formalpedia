-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a372_ae_smallcell_to_fullmask_energy_cross_Young_source
-- name    : AvramDividend.Classical.avram_ga_a372_ae_smallcell_to_fullmask_energy_cross_Young_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:31:05.761129+00:00
-- url     : https://prove2.me/theorems/c731b83e-bd34-4ea3-a314-4cb02a070ff2
-- title:
--   A.e. physical Gaussian small-cell positive Young bound controlled by full-stop raw energy, Hessian cross and finite discount allowance
-- statement:
--   Given almost-everywhere one-sided small-increment Taylor, local value Lipschitz and Hessian source bounds on cells wholly before a stopping time, the positive part of the finite discounted small-increment source sum is bounded almost surely by the full-mask raw energy weighted ε+η, the full-mask absolute Hessian raw-centred quadratic cross weighted M/2, and one deterministic nonnegative discount Young allowance (qΔL)²/(4η) per physical cell. This composes proved a368 and a366, and is the key finite-mesh interface between genuine original a371 source regularity and uniform expected small-cell budget a364/a361.
-- source:
--   Original Gaussian a368 AE finite-mask combined Young and a366 nested mask energy/cross extension.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a368_ae_masked_finite_Young_energy_cross_budget
import Theorems.Thm_AvramDividend_Classical_avram_ga_a366_nested_small_fullcell_mask_energy_cross_Young_count_budget
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a372_ae_smallcell_to_fullmask_energy_cross_Young_source
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (s u v d h r z : ℕ → Ω → ℝ)
    (q Δ δ ε η L M : ℝ)
    (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hδ : 0 < δ)
    (hε : 0 ≤ ε) (hη : 0 < η)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hTime : ∀ i ω, A i ω → 0 ≤ s i ω)
    (hTaylor : ∀ᵐ ω ∂P, ∀ i, A i ω → |r i ω| < δ →
      max (Real.exp (-(q*s i ω)) *
        (v i ω-u i ω-d i ω*r i ω-h i ω/2*(r i ω)^2)) 0 ≤
        ε*(r i ω)^2)
    (hLip : ∀ᵐ ω ∂P, ∀ i, A i ω → |r i ω| < δ →
      |v i ω-u i ω| ≤ L*|r i ω|)
    (hHess : ∀ᵐ ω ∂P, ∀ i, A i ω → |r i ω| < δ →
      |h i ω| ≤ M) :
    ∀ᵐ ω ∂P,
      max (∑ i ∈ S, if A i ω ∧ |r i ω| < δ then
        Real.exp (-(q*(s i ω+Δ)))*(v i ω-u i ω) -
          Real.exp (-(q*s i ω))*(d i ω*r i ω+h i ω/2*(z i ω)^2)
        else 0) 0 ≤
      (∑ i ∈ S, if A i ω then
        (ε+η)*(r i ω)^2 else 0) +
      (∑ i ∈ S, if A i ω then
        M/2*|(r i ω)^2-(z i ω)^2| else 0) +
      (S.card : ℝ) * ((q*Δ*L)^2/(4*η)) := by sorry
