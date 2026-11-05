-- Prove2me | Theorems.Thm_CountKSat_StepCount_holds_append
-- name    : CountKSat.StepCount.holds_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:46:45.262551+00:00
-- url     : https://prove2.me/theorems/2b0babb2-f4c3-4b0b-b14a-abb3a5980b09
-- title:
--   Step Count: holds append
-- statement:
--   A formula in two parts holds exactly if both parts hold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L41-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L41-L43

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

theorem CountKSat.StepCount.holds_append (v : PLit → Prop) (x y : PFml) : Holds v (x ++ y) ↔ Holds v x ∧ Holds v y := by sorry
