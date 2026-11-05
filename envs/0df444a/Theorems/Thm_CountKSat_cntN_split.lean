-- Prove2me | Theorems.Thm_CountKSat_cntN_split
-- name    : CountKSat.cntN_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:24.509437+00:00
-- url     : https://prove2.me/theorems/105b441c-523a-415a-8c60-bb427e09ed67
-- title:
--   Count KSat: cnt N split
-- statement:
--   The count of X ++ s is the count of the light child (H added) plus the count of the heavy child
--   (P added) with «H is false» on the side list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L113-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/StepCount.lean#L113-L123

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

theorem CountKSat.cntN_split (n : ℕ) (X s : PFml) (H : PCl) (P : PFml) (hP : ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q) :
    cntN n (X ++ s) = cntN n (X ++ addP [H] s) + cntN n ((negU H ++ X) ++ addP P s) := by sorry
