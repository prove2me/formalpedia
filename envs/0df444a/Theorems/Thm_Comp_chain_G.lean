-- Prove2me | Theorems.Thm_Comp_chain_G
-- name    : Comp.chain_G
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:59:24.207209+00:00
-- url     : https://prove2.me/theorems/90c8ec3d-7cf5-4d52-981d-a90894a5b8fb
-- title:
--   Comp: chain G
-- statement:
--   **The sure-safety region of the real-valued game, exactly.** `CSG.G`, a greatest fixed point of
--       an operator on `Set Chain` defined through `PMF.support`, is the cycle `{c0, c1}` -- established
--       from a computation that was run and observed to stop, with no bound on the number of iterations
--       and no appeal to any property of the search.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L318-L320
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L318-L320

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.chain_G :
    (chainGame.toCSG chainGame_wf).G (↑chainSafe : Set Chain) = (↑chainGood : Set Chain) := by sorry
