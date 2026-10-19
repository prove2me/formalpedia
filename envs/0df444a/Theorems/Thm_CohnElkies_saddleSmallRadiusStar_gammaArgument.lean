-- Prove2me | Theorems.Thm_CohnElkies_saddleSmallRadiusStar_gammaArgument
-- name    : CohnElkies.saddleSmallRadiusStar_gammaArgument
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.260927+00:00
-- url     : https://prove2.me/theorems/ef370f3a-d918-491f-b5de-7516b7955034
-- title:
--   CohnElkies.saddleSmallRadiusStar_gammaArgument
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

theorem CohnElkies.saddleSmallRadiusStar_gammaArgument
    {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    ((d : ℝ) / 2) *
        (1 + saddleSmallRadiusStarOrdinate ε d) / 2 =
      Real.log ((d : ℝ) / 2) / 8 := by sorry
