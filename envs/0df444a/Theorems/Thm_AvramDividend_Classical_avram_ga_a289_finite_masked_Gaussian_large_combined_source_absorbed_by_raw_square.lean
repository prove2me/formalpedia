-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a289_finite_masked_Gaussian_large_combined_source_absorbed_by_raw_square
-- name    : AvramDividend.Classical.avram_ga_a289_finite_masked_Gaussian_large_combined_source_absorbed_by_raw_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:16:59.649569+00:00
-- url     : https://prove2.me/theorems/a8b76d45-4859-44a1-8480-9b3e38d6ba12
-- title:
--   Large Gaussian combined finite-cell positive source dominated by endpoint exponential and raw-square tail
-- statement:
--   On a finite mask selecting true large Gaussian increments with absolute raw size at least δ and deterministic centring drift at most δ, the positive part of the discounted combined source finite sum is bounded by the sum of one-sided endpoint exponential envelopes plus an explicit constant B(1/δ²+1/δ+2) times the squared raw increment. This packages previously proved a260 and a261 into the exact two-source domination needed for a263, preserving the original signed combined residual.
-- source:
--   Avram zerojump Gaussian full-cell source a260+a261, large-cell HJB envelope and raw-square expected tails

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a260_finite_masked_gaussian_large_combined_positive_source_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a289_finite_masked_Gaussian_large_combined_source_absorbed_by_raw_square
    {Ω : Type*} (S : Finset ℕ)
    (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (e0 e1 w0 w1 d h r z T : ℕ → Ω → ℝ)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hCell : ∀ i ω, A i ω →
      0 ≤ e0 i ω ∧ e0 i ω ≤ 1 ∧
      0 ≤ e1 i ω ∧ e1 i ω ≤ 1 ∧
      0 ≤ T i ω ∧ |w0 i ω| ≤ B ∧
      |d i ω| ≤ B ∧ |h i ω| ≤ B ∧
      w1 i ω ≤ T i ω)
    (hLarge : ∀ i ω, A i ω → δ ≤ |r i ω|)
    (hDrift : ∀ i ω, A i ω → |r i ω-z i ω| ≤ δ)
    (ω : Ω) :
    max (∑ i ∈ S, if A i ω then
      e1 i ω*(w1 i ω-w0 i ω) -
        e0 i ω*(d i ω*r i ω+h i ω/2*(z i ω)^2)
      else 0) 0 ≤
    ∑ i ∈ S, if A i ω then
      T i ω+B*(1/δ^2+1/δ+2)*(r i ω)^2
      else 0 := by sorry
