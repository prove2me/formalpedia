-- Prove2me | Theorems.Thm_CohnElkies_saddleDigamma_add_nat
-- name    : CohnElkies.saddleDigamma_add_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:58.09238+00:00
-- url     : https://prove2.me/theorems/cdb9cf09-c6cb-4d88-8e7e-8ac582b73ab6
-- title:
--   CohnElkies.saddleDigamma_add_nat
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
open scoped Topology BigOperators

theorem CohnElkies.saddleDigamma_add_nat
    {m : ℝ} (hm : 0 < m) (n : ℕ) :
    saddleDigamma (m + (n : ℝ)) =
      saddleDigamma m +
        ∑ k ∈ Finset.range n,
          (m + (k : ℝ))⁻¹ := by sorry
