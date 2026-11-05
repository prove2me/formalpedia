-- Prove2me | Theorems.Thm_CountKSat_StepCount_pickK_petals
-- name    : CountKSat.StepCount.pickK_petals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:54:32.027091+00:00
-- url     : https://prove2.me/theorems/a7271d69-567b-4f7c-a539-f764976b23c7
-- title:
--   Step Count: pick K petals
-- statement:
--   Every petal Q that `pickK` returns comes from a clause of s whose literals lie in the heart or
--   in Q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L94-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L94-L105

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

theorem CountKSat.StepCount.pickK_petals {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {H : PCl} {P : PFml} (h : pickK θ k s = some (H, P)) :
    ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q := by sorry
