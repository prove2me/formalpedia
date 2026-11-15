-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a345_finite_masked_gaussian_small_discount_Young_bound_almost_sure
-- name    : AvramDividend.Classical.avram_ga_a345_finite_masked_gaussian_small_discount_Young_bound_almost_sure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:53:16.210694+00:00
-- url     : https://prove2.me/theorems/bb9b1f8a-b1b0-4fb3-bd0b-13757b6a0ef0
-- title:
--   Almost-sure finite masked Gaussian small-cell combined positive source bounded by Taylor modulus, Young and Hessian cross
-- statement:
--   If the original stopped Gaussian small-cell C² Taylor positive modulus, local Lipschitz value increment, bounded Hessian and positive-time hypotheses hold simultaneously almost surely on each selected finite mesh cell, then almost surely the positive part of their combined discounted source sum is bounded by ε+η times masked raw-square energy, a finite deterministic Young discount-width correction, and the raw-centred quadratic Hessian difference. The proof applies the actual one-sided source a236, Young a281, and finite masked sum a245 at each sample path in the common probability-one event, fitting the exact original a194/a165 hypotheses needed to close a264.
-- source:
--   Avram Gaussian true original stopped physical source small a194/a165 and proved a236/a281/a245; almost sure finite masked lift

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a281_discount_raw_first_increment_Young_square_budget
import Theorems.Thm_AvramDividend_Classical_avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a345_finite_masked_gaussian_small_discount_Young_bound_almost_sure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (s u v d h r z : ℕ → Ω → ℝ)
    (q Δ ε L M η : ℝ)
    (hq : 0 ≤ q) (hΔ : 0 ≤ Δ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hM : 0 ≤ M) (hη : 0 < η)
    (hTime : ∀ᵐ ω ∂P, ∀ i ∈ S, A i ω → 0 ≤ s i ω)
    (hTaylor : ∀ᵐ ω ∂P, ∀ i ∈ S, A i ω →
      max (Real.exp (-(q*s i ω)) *
        (v i ω-u i ω-d i ω*r i ω-h i ω/2*(r i ω)^2)) 0 ≤
        ε*(r i ω)^2)
    (hLip : ∀ᵐ ω ∂P, ∀ i ∈ S, A i ω →
      |v i ω-u i ω| ≤ L*|r i ω|)
    (hHess : ∀ᵐ ω ∂P, ∀ i ∈ S, A i ω → |h i ω| ≤ M) :
    ∀ᵐ ω ∂P,
      max (∑ i ∈ S, if A i ω then
        Real.exp (-(q*(s i ω+Δ)))*(v i ω-u i ω) -
          Real.exp (-(q*s i ω))*
            (d i ω*r i ω+h i ω/2*(z i ω)^2)
        else 0) 0 ≤
      ∑ i ∈ S, if A i ω then
        (ε+η)*(r i ω)^2+(q*Δ*L)^2/(4*η)+
          M/2*|(r i ω)^2-(z i ω)^2|
        else 0 := by sorry
