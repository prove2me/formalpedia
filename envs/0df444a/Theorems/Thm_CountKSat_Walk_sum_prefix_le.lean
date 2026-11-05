-- Prove2me | Theorems.Thm_CountKSat_Walk_sum_prefix_le
-- name    : CountKSat.Walk.sum_prefix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:44:13.19462+00:00
-- url     : https://prove2.me/theorems/204947e5-22e5-4659-b1b5-2aa53526ada4
-- title:
--   Walk: sum prefix le
-- statement:
--   The sum over a prefix of a list of numbers is at most the sum over the whole list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L43-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L43-L47

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

theorem CountKSat.Walk.sum_prefix_le (sel : τ → Option ν) (v : ν → ℕ) {l xs : List τ} (h : l <+: xs) :
    ((l.filterMap sel).map v).sum ≤ ((xs.filterMap sel).map v).sum := by sorry
