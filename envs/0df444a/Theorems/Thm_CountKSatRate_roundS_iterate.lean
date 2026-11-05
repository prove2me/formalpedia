-- Prove2me | Theorems.Thm_CountKSatRate_roundS_iterate
-- name    : CountKSatRate.roundS_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:37:09.641256+00:00
-- url     : https://prove2.me/theorems/c97844ab-2d16-40ef-9e94-955ac15fcfee
-- title:
--   Count KSat Rate: round S iterate
-- statement:
--   The state of the summing walk after i rounds: the stack of the plain walk, and the sum of the
--   values of the leaves that the plain walk has listed.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Walk.lean#L28-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Walk.lean#L28-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Walk
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open CountKSatRate
open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta)

theorem CountKSatRate.roundS_iterate {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (i : ℕ) (st out : List σ) :
    (roundS step val)^[i] (st, (out.map val).sum) =
      (((Sparsify.round step)^[i] (st, out)).1, (((Sparsify.round step)^[i] (st, out)).2.map val).sum) := by sorry
