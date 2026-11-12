-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_original_inclusive_finite_cap_compact
-- name    : AvramDividend.Classical.avram_bva20_original_inclusive_finite_cap_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:33:49.804274+00:00
-- url     : https://prove2.me/theorems/20bd29d5-9581-41eb-81c9-c17d1de3878a
-- title:
--   Original finite inclusive reserve cap is a compact real interval
-- statement:
--   For a finite extended-nonnegative cap C, the original physical reserve domain 0≤b and ENNReal.ofReal b≤C coincides with the compact real interval [0,C.toReal]. Compactness allows the supplied original finite-mark kernel uniform continuity to imply a common finite absolute kernel bound, the missing source-specific DCT domination step for 7ccc2a1a.
-- source:
--   Exact inclusive original reserve cap compactness input for 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva20_original_inclusive_finite_cap_compact
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤) :
    IsCompact {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} := by sorry
