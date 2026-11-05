-- Prove2me | Theorems.Thm_CountKSat_cntN_step
-- name    : CountKSat.cntN_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:45.198769+00:00
-- url     : https://prove2.me/theorems/15a4987f-e118-4405-949e-e87bae7afc19
-- title:
--   Count KSat: cnt N step
-- statement:
--   The count at a node is the sum of the counts at its two children.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L126-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L126-L130

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
open StepCount

theorem CountKSat.cntN_step {θ : ℕ → ℕ} {k : ℕ} (n : ℕ) {x l h : CNode} (hst : stepC θ k x = some (l, h)) :
    cntN n (leafF x) = cntN n (leafF l) + cntN n (leafF h) := by sorry
