-- Prove2me | Theorems.Thm_Coding_eq_replicate_of_bitsOf
-- name    : Coding.eq_replicate_of_bitsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:02:53.924611+00:00
-- url     : https://prove2.me/theorems/d79eac9e-6268-4d25-bec0-7c6d62939462
-- title:
--   Coding: eq replicate of bits Of
-- statement:
--   A string of λ bits that writes the index 0 is 0^λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L149-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L149-L153

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

theorem Coding.eq_replicate_of_bitsOf {w : List Bool} (hw : w.length = lam) (h : Grid.bitsOf lam w = fun _ => false) : w = List.replicate lam false := by sorry
