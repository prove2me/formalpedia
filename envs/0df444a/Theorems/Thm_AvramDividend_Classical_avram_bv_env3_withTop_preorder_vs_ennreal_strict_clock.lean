-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_withTop_preorder_vs_ennreal_strict_clock
-- name    : AvramDividend.Classical.avram_bv_env3_withTop_preorder_vs_ennreal_strict_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:47:51.794725+00:00
-- url     : https://prove2.me/theorems/4c86104e-b182-4d2d-a921-e85c91360389
-- title:
--   Exact strict-clock order agreement between WithTop-preorder and ENNReal for an original finite horizon
-- statement:
--   Although the two clock expressions share a WithTop NNReal carrier, their instances for strict comparison can differ: the source uses the generic WithTop preorder and the canonical target uses the ENNReal partial order. Prove the exact equivalence by splitting the target clock into top and finite cases and reducing finite comparison to the NNReal order.
-- source:
--   Source-exact original BV strict stopped witness adapter d23ad195 and full-atom signed mesh adapter 77ffa1ad; original Lean order instances visible in remote compiler diagnostics 28190 and 28193.

import Mathlib
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_withTop_preorder_vs_ennreal_strict_clock
    (S : ℝ≥0) (τ : ℝ≥0∞) :
    ((WithTop.some S : ℝ≥0∞) < τ) ↔ ((S : ℝ≥0∞) < τ) := by sorry
