-- Prove2me | Theorems.Thm_Comp_chain_iter4
-- name    : Comp.chain_iter4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:58:44.748007+00:00
-- url     : https://prove2.me/theorems/8c956676-cf01-4b60-a823-2f54817700c5
-- title:
--   Comp: chain iter4
-- statement:
--   Four steps from `Finset.univ` reach `chainGood`. Chained from the single steps rather than
--       evaluated in one go, so each `decide` stays small; the `(4 : ℕ) = 3 + 1` rewrites are only there
--       to let `Function.iterate_succ_apply` see through the numeral.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L305-L310
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L305-L310

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.chain_iter4 : (chainGame.gStepF chainSafe)^[4] Finset.univ = chainGood := by sorry
