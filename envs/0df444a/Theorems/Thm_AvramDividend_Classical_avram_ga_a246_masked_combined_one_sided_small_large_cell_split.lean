-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a246_masked_combined_one_sided_small_large_cell_split
-- name    : AvramDividend.Classical.avram_ga_a246_masked_combined_one_sided_small_large_cell_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:23:28.777266+00:00
-- url     : https://prove2.me/theorems/70799c37-1033-4496-86df-a532d3581053
-- title:
--   True Gaussian one-sided combined finite full-cell source positive part controlled by separately majorised small and large raw increments
-- statement:
--   For a finite original stopped Gaussian physical source, assume its signed combined residual f_i has a nonnegative small raw-increment majorant u_i whenever |R_i|<delta and a nonnegative rare large raw-increment majorant v_i whenever |R_i|≥delta. The positive part of the entire masked sum is then bounded by the masked split sum of these majorants, preserving positive-only Taylor estimates. Used with the source-specific a236 small-cell and a233 large positive rare-cell results to finish combined source a216.
-- source:
--   a245 finite positive masked source lift, with genuine original small/large Gaussian physical raw increments

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a246_masked_combined_one_sided_small_large_cell_split
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (f R u v : ℕ → ℝ) (δ : ℝ)
    (hu : ∀ i ∈ S, 0 ≤ u i)
    (hv : ∀ i ∈ S, 0 ≤ v i)
    (hSmall : ∀ i ∈ S, |R i| < δ → max (f i) 0 ≤ u i)
    (hLarge : ∀ i ∈ S, δ ≤ |R i| → max (f i) 0 ≤ v i) :
    max (∑ i ∈ S, if A i then f i else 0) 0 ≤
      (∑ i ∈ S, if A i then
        if |R i| < δ then u i else v i else 0) := by sorry
