-- Prove2me | Theorems.Thm_Coding_idxOf_lt_iff
-- name    : Coding.idxOf_lt_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:04:09.455608+00:00
-- url     : https://prove2.me/theorems/e6f3e883-8b43-4651-b9b2-751d3e46d545
-- title:
--   Coding: idx Of lt iff
-- statement:
--   In a list along which f increases, the order of the positions is the order of the values of f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L66-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L66-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Coding_OccLists
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_idxOf
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.idxOf


set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count

theorem Coding.idxOf_lt_iff {α : Type} [BEq α] [LawfulBEq α] {f : α → ℕ} {l : List α} (hl : l.Pairwise fun x y => f x < f y) {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    l.idxOf x < l.idxOf y ↔ f x < f y := by sorry
