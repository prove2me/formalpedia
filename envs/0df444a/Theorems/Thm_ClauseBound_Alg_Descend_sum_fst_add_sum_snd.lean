-- Prove2me | Theorems.Thm_ClauseBound_Alg_Descend_sum_fst_add_sum_snd
-- name    : ClauseBound.Alg.Descend.sum_fst_add_sum_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:05.453237+00:00
-- url     : https://prove2.me/theorems/7e8b5e80-5266-4fa6-a977-91dad06dfbca
-- title:
--   Descend: sum fst add sum snd
-- statement:
--   If D·Z(a) is the first component of e(a) plus the sum of z over the second, for every member a
--   of w, then D times the sum of Z over w is the sum of all first components
--   plus the sum of z over all second components.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L47-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/Descend.lean#L47-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_Descend
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_ClauseBound_Alg_Descend
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists

theorem ClauseBound.Alg.Descend.sum_fst_add_sum_snd {α β : Type} (w : List α) (e : α → ℤ × List β) (Z : α → ℤ) (z : β → ℤ) (D : ℤ)
    (h : ∀ a ∈ w, D * Z a = (e a).1 + ((e a).2.map z).sum) :
    ((w.map e).map Prod.fst).sum + (((w.map e).flatMap Prod.snd).map z).sum = D * (w.map Z).sum := by sorry
