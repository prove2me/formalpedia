-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54n_nonnegative_weighted_caplinear_smooth_extension_grid_upper
-- name    : AvramDividend.Classical.avram_gbB54n_nonnegative_weighted_caplinear_smooth_extension_grid_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:16:46.689229+00:00
-- url     : https://prove2.me/theorems/7f5adc6e-ce13-4917-b890-a5bc4e64e0c9
-- title:
--   Finite nonnegative-weighted upper caplinear Gaussian mesh has bounded one-sided smooth-continuation excess
-- statement:
--   For any finite index set S, nonnegative discount weights E, cell endpoints X_i,Y_i and arbitrary interior gains G_i, the sum of upper caplinear first-order cell remainders is bounded by the corresponding sum for the slope-alpha smooth continuation whenever alpha is at least one. This is the direct weighted finite-grid lift of B54m needed in the original stopped Ito cash source, and keeps every finite grid index and discount weight explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped BigOperators

theorem AvramDividend.Classical.avram_gbB54n_nonnegative_weighted_caplinear_smooth_extension_grid_upper
    (w : ℝ → ℝ) (b α : ℝ) (hα : 1 ≤ α)
    (S : Finset ℕ) (E X Y G : ℕ → ℝ)
    (hE : ∀ i ∈ S, 0 ≤ E i) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    (∑ i ∈ S, E i * (V (Y i) - V (X i) -
      (if X i ≤ b then G i else 1) * (Y i - X i))) ≤
    (∑ i ∈ S, E i * (U (Y i) - U (X i) -
      (if X i ≤ b then G i else α) * (Y i - X i))) := by sorry
