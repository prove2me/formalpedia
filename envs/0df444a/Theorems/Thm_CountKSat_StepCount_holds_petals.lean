-- Prove2me | Theorems.Thm_CountKSat_StepCount_holds_petals
-- name    : CountKSat.StepCount.holds_petals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:55:10.533859+00:00
-- url     : https://prove2.me/theorems/c8c669b6-9389-4cc5-9462-efa3d5fe7c43
-- title:
--   Step Count: holds petals
-- statement:
--   If no literal of the heart H is true and s holds, then the petals hold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L67-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L67-L74

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

theorem CountKSat.StepCount.holds_petals {v : PLit → Prop} {s P : PFml} {H : PCl} (hP : ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q)
    (hH : ¬ ∃ l ∈ H, v l) (hs : Holds v s) : Holds v P := by sorry
