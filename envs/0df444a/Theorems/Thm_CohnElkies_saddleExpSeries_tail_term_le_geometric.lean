-- Prove2me | Theorems.Thm_CohnElkies_saddleExpSeries_tail_term_le_geometric
-- name    : CohnElkies.saddleExpSeries_tail_term_le_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/3e093827-a468-46f6-aed8-0c66a30f683a
-- title:
--   CohnElkies.saddleExpSeries_tail_term_le_geometric
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

theorem CohnElkies.saddleExpSeries_tail_term_le_geometric
    {y : ℝ} (hy : 0 ≤ y)
    (m : ℕ) (hym : 2 * y ≤ (m : ℝ) + 1)
    (k : ℕ) :
    y ^ (m + k) / ((m + k).factorial : ℝ) ≤
      (y ^ m / (m.factorial : ℝ)) *
        ((1 / 2 : ℝ) ^ k) := by sorry
