-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb32_finite_cap_closed_interval_compact
-- name    : AvramDividend.Classical.avram_bvb32_finite_cap_closed_interval_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:13:06.095823+00:00
-- url     : https://prove2.me/theorems/d6e6387b-7389-4bcb-a1ca-ed1c1a988bfe
-- title:
--   Finite ENNReal reserve cap has compact closed real state interval
-- statement:
--   For finite extended nonnegative C, the inclusive closed real reserve cap {b≥0, ofReal b≤C} is exactly [0,C.toReal] and hence compact. Used for source-exact original stopped negative-mark kernel measurability.
-- source:
--   Pinned Mathlib ENNReal.ofReal_le_iff_le_toReal and real isCompact_Icc; original BV finite cap measurability.

import Mathlib
open Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb32_finite_cap_closed_interval_compact
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤) :
    IsCompact {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} := by sorry
