-- Prove2me | Theorems.Thm_Comp_LeakyGate_gate_afInner_at_univ
-- name    : Comp.LeakyGate.gate_afInner_at_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:46:24.542808+00:00
-- url     : https://prove2.me/theorems/b03b2a57-4be5-4107-b21e-19d0a2d3e8fa
-- title:
--   Leaky Gate: gate af Inner at univ
-- statement:
--   The first outer step's inner `μX` fixed point, at `Finset.univ`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L215-L219
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L215-L219

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate

theorem Comp.LeakyGate.gate_afInner_at_univ :
    ((gate.toCsgQ.toCSG gate_wf).AFInner ↑gateTarget
        ↑(Finset.univ : Finset (Fin gate.nStates))).lfp = (↑gateGood : Set (Fin gate.nStates)) := by sorry
