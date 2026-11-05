-- Prove2me | Theorems.Thm_CountKSat_Walk_foldl_add_sel
-- name    : CountKSat.Walk.foldl_add_sel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:44:16.581683+00:00
-- url     : https://prove2.me/theorems/a3c96758-1864-478d-bd23-11885e41b5e7
-- title:
--   Walk: foldl add sel
-- statement:
--   The loop's fold adds v over the points that sel picks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L34-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L34-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Poly_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_Walk
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.Stepped Groundwork.Sparsify
variable {α ν : Type}
open CountKSat.Walk
variable {τ : Type}

theorem CountKSat.Walk.foldl_add_sel (sel : τ → Option ν) (v : ν → ℕ) (xs : List τ) (c : ℕ) :
    xs.foldl (fun c x => c + ((sel x).map v).getD 0) c = c + ((xs.filterMap sel).map v).sum := by sorry
