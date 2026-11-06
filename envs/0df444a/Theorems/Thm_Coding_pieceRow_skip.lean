-- Prove2me | Theorems.Thm_Coding_pieceRow_skip
-- name    : Coding.pieceRow_skip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:04:21.016197+00:00
-- url     : https://prove2.me/theorems/2a087614-6f02-4af7-a919-8797fca21186
-- title:
--   Coding: piece Row skip
-- statement:
--   At the positions other than its own, a grid point holds the strings of z.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L107-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L107-L111

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_GridDefs
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_Eight_SecLevel_GridWords
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Grid
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}

theorem Coding.pieceRow_skip (a : ℕ) (z : List Bool) (x u' : ℕ) : pieceRow g tr lam a z x (if u' < nodeG g tr a x then u' else u' + 1) = block lam u' (block ((g * g - 1) * lam) x z) := by sorry
