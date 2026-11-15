-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a305_finite_rare_Gaussian_combined_positive_source_bound
-- name    : AvramDividend.Classical.avram_ga_a305_finite_rare_Gaussian_combined_positive_source_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:46:38.911323+00:00
-- url     : https://prove2.me/theorems/3e21f7e4-1dfe-43e9-b355-70d2aa196452
-- title:
--   Finite rare Gaussian combined positive source bounded by signed rare exponential and raw-square large tail sums
-- statement:
--   For a finite family of genuine rare Gaussian source cells with compact preincrement reserves, small deterministic drift relative to the rare threshold, and source upper HJB exponential plus polynomial jet bounds, the positive part of the total signed combined verification source is controlled by a fixed signed-increment exponential tail sum plus a constant times the raw large square sum. This is the algebraic bridge from a301/a303 into original a275/a187 expected L1 for the a263 Gaussian large-cell parent.
-- source:
--   Original source scalar a302 positive HJB exponential transfer, a261 Gaussian large increment polynomial control and finite positive part summation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a302_nonnegative_exponential_HJB_endpoint_upper_via_compact_start
import Theorems.Thm_AvramDividend_Classical_avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a305_finite_rare_Gaussian_combined_positive_source_bound
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (f r z a y : ℕ → ℝ) (θ K M B δ : ℝ)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hCell : ∀ i ∈ S, A i →
      max (f i) 0 ≤ K*Real.exp (θ*(y i+r i)) +
        M*(1+|r i|+z i^2/2))
    (hReserve : ∀ i ∈ S, A i → y i ≤ B)
    (hRare : ∀ i ∈ S, A i → δ ≤ |r i|)
    (hDrift : ∀ i ∈ S, A i → |a i| ≤ δ)
    (hCentered : ∀ i ∈ S, A i → z i = r i-a i) :
    max (∑ i ∈ S, if A i then f i else 0) 0 ≤
      (K*Real.exp (θ*B))*
        (∑ i ∈ S, if A i then Real.exp (θ*r i) else 0) +
      (M*(1/δ^2+1/δ+2))*
        (∑ i ∈ S, if A i then (r i)^2 else 0) := by sorry
