-- Prove2me | Theorems.Thm_CountKSat_StepCount_holds_singleton
-- name    : CountKSat.StepCount.holds_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:54:46.353263+00:00
-- url     : https://prove2.me/theorems/7c1e7590-d341-430f-a644-4f9845d978df
-- title:
--   Step Count: holds singleton
-- statement:
--   A formula with the one clause H holds exactly if a literal of H is true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L57-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L57-L57

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

theorem CountKSat.StepCount.holds_singleton (v : PLit → Prop) (H : PCl) : Holds v [H] ↔ ∃ l ∈ H, v l := by sorry
