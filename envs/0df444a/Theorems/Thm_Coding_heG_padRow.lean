-- Prove2me | Theorems.Thm_Coding_heG_padRow
-- name    : Coding.heG_padRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:29:51.751022+00:00
-- url     : https://prove2.me/theorems/de63454a-e237-41e1-bd73-1c51b26afb93
-- title:
--   Coding: he G pad Row
-- statement:
--   The strings of the padded setting.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L102-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L102-L104

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}

theorem Coding.heG_padRow (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) {x u : ℕ} (hx : x < g) (hu : u < g * g) :
    heG g g lam (padRow g tr lam a.val z) x u = pieceRow g tr lam a.val z x u := by sorry
