-- Prove2me | Theorems.Thm_CountKSat_cntN_root
-- name    : CountKSat.cntN_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:51.943177+00:00
-- url     : https://prove2.me/theorems/2a74ed4f-d553-4215-a96b-b7bb8335a8c8
-- title:
--   Count KSat: cnt N root
-- statement:
--   The count at the root of the tree of ψ is the count of ψ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L133-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L133-L148

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

theorem CountKSat.cntN_root (n : ℕ) (ψ : Fml) : cntN n (leafF (rootC (List.replicate n (), ψ))) = cntN n ψ := by sorry
