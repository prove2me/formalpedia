-- Prove2me | Theorems.Thm_CohnElkies_manuscriptQuotientRootInf_div_sqrt_eq
-- name    : CohnElkies.manuscriptQuotientRootInf_div_sqrt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.329542+00:00
-- url     : https://prove2.me/theorems/7070d977-bc02-4414-a5ae-5720924c6551
-- title:
--   CohnElkies.manuscriptQuotientRootInf_div_sqrt_eq
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
open Filter
open scoped Topology

theorem CohnElkies.manuscriptQuotientRootInf_div_sqrt_eq (d : ℕ) :
    sInf (manuscriptQuotientRootSet d) / Real.sqrt (d : ℝ) =
      normalizedProgram d := by sorry
