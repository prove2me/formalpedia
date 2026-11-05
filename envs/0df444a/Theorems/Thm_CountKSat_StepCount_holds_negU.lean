-- Prove2me | Theorems.Thm_CountKSat_StepCount_holds_negU
-- name    : CountKSat.StepCount.holds_negU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:54:49.11219+00:00
-- url     : https://prove2.me/theorems/1abb1554-2927-4909-bf63-ebb80be84e96
-- title:
--   Step Count: holds neg U
-- statement:
--   The unit clauses `negU H` hold under an assignment b exactly if b makes no literal of H true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L60-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L60-L64

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

theorem CountKSat.StepCount.holds_negU (b : ℕ → Bool) (H : PCl) : Holds (fun l => b l.1 = l.2) (negU H) ↔ ¬ ∃ l ∈ H, b l.1 = l.2 := by sorry
