-- Prove2me | Theorems.Thm_Coding_length_block_row
-- name    : Coding.length_block_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:29:48.594023+00:00
-- url     : https://prove2.me/theorems/f714ecbb-2890-41d0-bbcc-0d567228843f
-- title:
--   Coding: length block row
-- statement:
--   The part of z for the x-th grid point of the row has (g² − 1)λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L76-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L76-L77

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

theorem Coding.length_block_row {z : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) {x : ℕ} (hx : x < g) : (block ((g * g - 1) * lam) x z).length = (g * g - 1) * lam := by sorry
