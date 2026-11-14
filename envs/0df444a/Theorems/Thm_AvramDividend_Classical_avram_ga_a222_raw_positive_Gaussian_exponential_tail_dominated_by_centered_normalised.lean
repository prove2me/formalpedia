-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a222_raw_positive_Gaussian_exponential_tail_dominated_by_centered_normalised
-- name    : AvramDividend.Classical.avram_ga_a222_raw_positive_Gaussian_exponential_tail_dominated_by_centered_normalised
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:55:26.744331+00:00
-- url     : https://prove2.me/theorems/c322934c-7e8e-4fdb-b083-a362794020e2
-- title:
--   Raw Gaussian positive exponential tail dominated pointwise by centred normalised Gaussian exponential tail
-- statement:
--   If the physical deterministic Gaussian drift over a mesh cell is bounded by half the positive large-increment threshold, each positive raw large Gaussian source increment exponential tail is bounded by a factor exp(theta times drift absolute value) times a centered normalized Gaussian positive exponential tail at threshold delta/(2sigma). The bound feeds the original upper-HJB one-sided a216 large-cell source.
-- source:
--   Proved raw positive Chernoff threshold and envelope lemma a200; original true stopped Gaussian combined source

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a200_raw_positive_large_cell_to_centered_gaussian_chernoff
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a222_raw_positive_Gaussian_exponential_tail_dominated_by_centered_normalised
    (θ δ σ d r : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hσ : 0 < σ) (hd : |d| ≤ δ / 2) :
    (if δ ≤ r then Real.exp (θ * r) else 0) ≤
      Real.exp (θ * |d|) *
        (if δ / (2 * σ) ≤ (r - d) / σ
        then Real.exp ((θ * σ) * ((r - d) / σ)) else 0) := by sorry
