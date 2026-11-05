-- Prove2me | Theorems.Thm_CountKSat_StepCount_holds_addP
-- name    : CountKSat.StepCount.holds_addP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:52:55.591205+00:00
-- url     : https://prove2.me/theorems/1bff7498-e0f8-4850-870a-008bfeba61db
-- title:
--   Step Count: holds add P
-- statement:
--   `addP A s` holds exactly if A and s hold: a clause that `addP` drops contains a clause of A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L46-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L46-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Tauto
import Definitions.Def_CountKSat_StepCount
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.StepCount

theorem CountKSat.StepCount.holds_addP (v : PLit → Prop) (A s : PFml) : Holds v (addP A s) ↔ Holds v A ∧ Holds v s := by sorry
