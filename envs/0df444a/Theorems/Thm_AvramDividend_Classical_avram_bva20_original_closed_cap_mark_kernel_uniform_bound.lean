-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_original_closed_cap_mark_kernel_uniform_bound
-- name    : AvramDividend.Classical.avram_bva20_original_closed_cap_mark_kernel_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:43:18.253204+00:00
-- url     : https://prove2.me/theorems/2fd66d45-3019-4f8e-b31b-7d9081bd9c0c
-- title:
--   Original finite closed-cap negative-mark kernel has a uniform absolute bound
-- statement:
--   The original finiteness and compact-subset uniform continuity assumptions for the integrated negative-mark gain imply a single nonnegative real absolute bound throughout the full inclusive physical reserve cap. The cap is compact by child 20bd29d5, and the kernel is continuous on it, so the Mathlib compact continuous boundedness theorem supplies B. This B controls every frozen uniform-grid and stopped physical compensator integrand after discounting via Proved theorem 401b54e0. Necessary to discharge the domination premise of paired DCT ca1a8182 and close 7ccc2a1a.
-- source:
--   Original inclusive-cap finite-mark uniform bound, a substantive analytic DCT prerequisite of 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva20_original_inclusive_finite_cap_compact
open Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva20_original_closed_cap_mark_kernel_uniform_bound
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤) (ψ : ℝ → ℝ)
    (hKernel : ∀ s : Set ℝ, IsCompact s →
      s ⊆ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} →
      UniformContinuousOn ψ s) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ b : ℝ, 0 ≤ b → ENNReal.ofReal b ≤ C → |ψ b| ≤ B := by sorry
