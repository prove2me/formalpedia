-- Prove2me | Theorems.Thm_CohnElkies_upperCosLaplaceKernel_integrable
-- name    : CohnElkies.upperCosLaplaceKernel_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:56.845665+00:00
-- url     : https://prove2.me/theorems/5772dfa9-0091-4dd4-bc58-c9ff1bcf58e4
-- title:
--   CohnElkies.upperCosLaplaceKernel_integrable
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

theorem CohnElkies.upperCosLaplaceKernel_integrable
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    IntegrableOn (upperCosLaplaceKernel c T) (Ioi 0) := by sorry
