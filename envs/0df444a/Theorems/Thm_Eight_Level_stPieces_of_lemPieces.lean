-- Prove2me | Theorems.Thm_Eight_Level_stPieces_of_lemPieces
-- name    : Eight.Level.stPieces_of_lemPieces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:57:17.789738+00:00
-- url     : https://prove2.me/theorems/e408dcac-5c76-47cc-bbf0-ecbb821e2e71
-- title:
--   Level: st Pieces of lem Pieces
-- statement:
--   The same, with part (a) taken from `LemPieces` (its fields `a_sum` and `a_abs`); part (b) for
--   the programs stays a hypothesis (`hF`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Pieces.lean#L56-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/Pieces.lean#L56-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Pieces
set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Finset

theorem Eight.Level.stPieces_of_lemPieces (h2 : LemPieces) (hF : StFact) : StPieces := by sorry
