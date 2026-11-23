-- Prove2me | Theorems.Thm_Comp_LeakyGate_gate_answers
-- name    : Comp.LeakyGate.gate_answers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:46:28.03205+00:00
-- url     : https://prove2.me/theorems/784786cf-7c8c-4808-a037-b8323ba63cf7
-- title:
--   Leaky Gate: gate answers
-- statement:
--   **A probabilistic model, computed and checked.** The sure-safety region of a game whose kernel
--       contains halves, as an answer to an objective, with both fixed-point checks closed by `decide`.
--
--       The weights took part in the three validity theorems above and nowhere else: the descent itself
--       never evaluated one. That is what makes the `decide`s possible, and it is the point of the whole
--       sparse layer.
--
--       No iteration count and no fixed-point check: `gRegion` runs `Comp/FixLoop.lean`'s loop --
--       apply, compare, stop -- which is proved to terminate at a fixed point, so the single `decide`
--       states only which region came back and the `#eval`s above are illustrative.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L170-L173
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/LeakyGateQ.lean#L170-L173

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_LeakyGateQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.LeakyGate

theorem Comp.LeakyGate.gate_answers :
    gate.toCsgQ.Answers gate_wf (Objective.sureSafe gateSafe) (Answer.region gateGood) := by sorry
