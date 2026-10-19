-- Prove2me | Theorems.Thm_CohnElkies_tendsto_log_factorialStirlingSequence
-- name    : CohnElkies.tendsto_log_factorialStirlingSequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:02.02251+00:00
-- url     : https://prove2.me/theorems/4140db58-cfbe-47bb-b4d2-106c58a5aa7c
-- title:
--   CohnElkies.tendsto_log_factorialStirlingSequence
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
open scoped Nat Topology

theorem CohnElkies.tendsto_log_factorialStirlingSequence :
    Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq k))
      atTop (nhds (Real.log (Real.sqrt Real.pi))) := by sorry
