-- Prove2me | Theorems.Thm_Coding_length_rowPart
-- name    : Coding.length_rowPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:29:30.678822+00:00
-- url     : https://prove2.me/theorems/9f950cd3-52e3-4de1-816d-33c412f4f151
-- title:
--   Coding: length row Part
-- statement:
--   The part of the padded setting for one grid point has g²λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L92-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L92-L94

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
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}

theorem Coding.length_rowPart (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) {x : ℕ} (hx : x < g) :
    ((List.range (g * g)).flatMap fun u => pieceRow g tr lam a.val z x u).length = g * g * lam := by sorry
