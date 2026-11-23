-- Prove2me | Theorems.Thm_Comp_HideOrRunData_hrd_separation
-- name    : Comp.HideOrRunData.hrd_separation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:47:24.584969+00:00
-- url     : https://prove2.me/theorems/0f8beacf-2d6e-4242-b23e-ae3077be4fbf
-- title:
--   Hide Or Run Data: hrd separation
-- statement:
--   **The gap, from a model given as data.** The stand-off is a value-1 state for reaching the goal
--       from which no strategy wins almost surely.
--
--       Both halves come out of the `Answers` relation through `Comp/Objective.lean`'s extraction
--       lemmas, which is what they are for: two objectives go in as data, two set equalities come back,
--       and the statement below assumes nothing that was not computed.
--
--       `SetLike.mem_coe` strips the `Finset`-to-`Set` coercion and `decide` finishes. The second half
--       needs the state count: in `Fin n` the elements `0` and `1` are equal exactly when `n = 1`, so
--       `0 ≠ 1` here is `hrd.nStates ≠ 1`, which is why it is `decide` and not `simp`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L213-L224
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunDataQ.lean#L213-L224

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData

theorem Comp.HideOrRunData.hrd_separation :
    (0 : Fin hrd.nStates) ∈ (hrd.toCsgQ.toCSG hrd_wf).LF ↑hrdTarget ∧
      (0 : Fin hrd.nStates) ∉ (hrd.toCsgQ.toCSG hrd_wf).AF ↑hrdTarget := by sorry
