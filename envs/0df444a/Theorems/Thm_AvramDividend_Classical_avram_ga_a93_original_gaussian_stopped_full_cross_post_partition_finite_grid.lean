-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a93_original_gaussian_stopped_full_cross_post_partition_finite_grid
-- name    : AvramDividend.Classical.avram_ga_a93_original_gaussian_stopped_full_cross_post_partition_finite_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:15:32.16424+00:00
-- url     : https://prove2.me/theorems/6459d12c-6891-4fcf-b0f7-1f1620b7751d
-- title:
--   Original stopped Gaussian physical source residual partitions exactly into full pre-stop and true crossing cells with post-stop zero
-- statement:
--   On the original stopped Gaussian physical grid, any source cell residual that agrees with the true full-cell expression before stop, the actual clipped crossing expression when the stop falls in a cell, and zero for post-stop cells has its total sum exactly equal to the full-mask sum plus crossing-mask sum.
-- source:
--   Direct original b0d9951c source-faithful finite stopped-grid reduction using full ga_a71, crossing ga_a72, poststop ga_a89 and unique crossing ga_a91.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a93_original_gaussian_stopped_full_cross_post_partition_finite_grid
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ ρ : ℝ≥0)
    (U F C : ℕ → ℝ)
    (hFull : ∀ i, s i < ρ → s i + Δ ≤ ρ → U i = F i)
    (hCross : ∀ i, s i < ρ → ρ < s i + Δ → U i = C i)
    (hPost : ∀ i, ρ ≤ s i → U i = 0) :
    (∑ i ∈ S, U i) =
      (∑ i ∈ S, if s i < ρ ∧ s i + Δ ≤ ρ then F i else 0) +
      (∑ i ∈ S, if s i < ρ ∧ ρ < s i + Δ then C i else 0) := by sorry
