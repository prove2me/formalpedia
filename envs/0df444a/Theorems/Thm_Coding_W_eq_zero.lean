-- Prove2me | Theorems.Thm_Coding_W_eq_zero
-- name    : Coding.W_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:04:25.354059+00:00
-- url     : https://prove2.me/theorems/2bebb826-440f-409d-9052-1a8990192d95
-- title:
--   Coding: W eq zero
-- statement:
--   W_a is 0 unless the string at each grid point's own position writes the index 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L156-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L156-L165

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

theorem Coding.W_eq_zero (yι : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (a : Fin (nParts g g tr)) (y : List Bool) (i : Fin (nMemb g g tr))
    (h : Grid.bitsOf lam (heG g g lam y i.val (nodeG g tr a.val i.val)) ≠ fun _ => false) : (levelNetP g tr lam yι Rm).W a y = 0 := by sorry
