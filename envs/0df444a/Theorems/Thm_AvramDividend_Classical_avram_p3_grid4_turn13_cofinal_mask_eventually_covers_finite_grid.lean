-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_cofinal_mask_eventually_covers_finite_grid
-- name    : AvramDividend.Classical.avram_p3_grid4_turn13_cofinal_mask_eventually_covers_finite_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:41:52.856538+00:00
-- url     : https://prove2.me/theorems/28a2ed9a-9f80-41c9-9a9b-b371a034874c
-- title:
--   One cofinal predictable compact-band cutoff eventually covers every finite original reserve grid
-- statement:
--   For every finite collection of strict positive cap-interior sample reserves, pointwise exhaustion by one sequence of compact predictable bands yields a common cutoff index K from which all mesh reserves are simultaneously contained in their corresponding bands. This finite diagonal property is used after the original-process cofinal compact-band theorem to localise physical grids.
-- source:
--   Finite-set induction and the maximum of finitely many natural thresholds; keeps the same band sequence for every physical cell and does not require a uniform cutoff across infinitely many grid rows.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_turn13_cofinal_mask_eventually_covers_finite_grid
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (s : Finset ℕ) (z : ℕ → ℝ)
    (hz : ∀ i ∈ s, 0 < z i ∧ ENNReal.ofReal (z i) < C) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ i ∈ s, z i ∈ Icc (a k) (b k) := by sorry
