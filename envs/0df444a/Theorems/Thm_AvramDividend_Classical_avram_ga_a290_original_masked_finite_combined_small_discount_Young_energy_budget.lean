-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a290_original_masked_finite_combined_small_discount_Young_energy_budget
-- name    : AvramDividend.Classical.avram_ga_a290_original_masked_finite_combined_small_discount_Young_energy_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:20:10.1582+00:00
-- url     : https://prove2.me/theorems/6a988c78-b640-48b3-b826-246766fcbf23
-- title:
--   Masked Gaussian combined small-source finite mesh positive error bounded by modulus energy, Young discount correction and raw-centred cross
-- statement:
--   For a finite physical Gaussian cell mask selecting only stopping and small-raw-increment cells, assume the one-sided weighted Taylor remainder, compact source local Lipschitz value increment, bounded Hessian and nonnegative time apply on selected cells. The positive part of the combined discounted source sum is then bounded by the masked squared raw Gaussian energy weighted by ε+η, a finite Young discount-width correction, and the raw-versus-centred quadratic Hessian cross. This preserves the true original stopping mask and supplies a direct pointwise source for a264.
-- source:
--   Proved original Gaussian a236, a245, a281, HJB small source a264

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
import Theorems.Thm_AvramDividend_Classical_avram_ga_a281_discount_raw_first_increment_Young_square_budget
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a290_original_masked_finite_combined_small_discount_Young_energy_budget
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (s u v d h r z : ℕ → Ω → ℝ)
    (q Δ ε L M η : ℝ)
    (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hη : 0 < η)
    (hTime : ∀ i ω, A i ω → 0 ≤ s i ω)
    (hTaylor : ∀ i ω, A i ω →
      max (Real.exp (-(q*s i ω)) *
        (v i ω-u i ω-d i ω*r i ω-h i ω/2*(r i ω)^2)) 0 ≤
        ε*(r i ω)^2)
    (hLip : ∀ i ω, A i ω →
      |v i ω-u i ω| ≤ L*|r i ω|)
    (hHess : ∀ i ω, A i ω → |h i ω| ≤ M)
    (ω : Ω) :
    max (∑ i ∈ S, if A i ω then
      Real.exp (-(q*(s i ω+Δ)))*(v i ω-u i ω) -
        Real.exp (-(q*s i ω))*
          (d i ω*r i ω+h i ω/2*(z i ω)^2)
      else 0) 0 ≤
    ∑ i ∈ S, if A i ω then
      (ε+η)*(r i ω)^2+(q*Δ*L)^2/(4*η)+
        M/2*|(r i ω)^2-(z i ω)^2|
      else 0 := by sorry
