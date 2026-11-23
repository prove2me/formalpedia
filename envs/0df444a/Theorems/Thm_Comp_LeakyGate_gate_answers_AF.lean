-- Prove2me | Theorems.Thm_Comp_LeakyGate_gate_answers_AF
-- name    : Comp.LeakyGate.gate_answers_AF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:45.456922+00:00
-- url     : https://prove2.me/theorems/1e4d0426-e3d3-4d89-a3dc-f24e100f9cb3
-- title:
--   Leaky Gate: gate answers AF
-- statement:
--   **Almost-sure reachability, computed from the model.** `{0, 1}` is its own inner `μX` fixed
--       point and the descent has reached it, so it *is* `CSG.AF {0}` -- and the nested loops of
--       `Comp/FixLoop.lean` find it without being told how far either of them has to go.
--
--       The single `decide` names the region; that it is the inner `μX` fixed point and that the outer
--       descent has reached it are theorems rather than hypotheses. The three lemmas above exhibit the
--       same run through the counted interface.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L234-L237
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L234-L237

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate

theorem Comp.LeakyGate.gate_answers_AF :
    gate.toCsgQ.Answers gate_wf (Objective.almostReach gateTarget) (Answer.region gateGood) := by sorry
