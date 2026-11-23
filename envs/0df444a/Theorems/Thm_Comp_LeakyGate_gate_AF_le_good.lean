-- Prove2me | Theorems.Thm_Comp_LeakyGate_gate_AF_le_good
-- name    : Comp.LeakyGate.gate_AF_le_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:29.755117+00:00
-- url     : https://prove2.me/theorems/c0d2f71c-ff5b-4025-a60b-19bca91155e1
-- title:
--   Leaky Gate: gate AF le good
-- statement:
--   …so `{0, 1}` bounds `AF` from above.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L222-L225
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L222-L225

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate

theorem Comp.LeakyGate.gate_AF_le_good :
    (gate.toCsgQ.toCSG gate_wf).AF ↑gateTarget ≤ (↑gateGood : Set (Fin gate.nStates)) := by sorry
