-- Prove2me | Theorems.Thm_CountKSatRate_roundS_iterate_of_le
-- name    : CountKSatRate.roundS_iterate_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:45:26.229247+00:00
-- url     : https://prove2.me/theorems/42cc769e-ffc6-43f7-b971-cbb3afaabe21
-- title:
--   Count KSat Rate: round S iterate of le
-- statement:
--   After at least 2·(number of leaves) − 1 rounds the stack is empty and the number is the sum of
--   the values of the leaves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Walk.lean#L51-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Walk.lean#L51-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Walk
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open CountKSatRate
open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta)

theorem CountKSatRate.roundS_iterate_of_le {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ)
    (hd : ∀ x ∈ leaves step d s, step x = none) (R : ℕ) (hR : 2 * (leaves step d s).length - 1 ≤ R) :
    (roundS step val)^[R] ([s], 0) = ([], ((leaves step d s).map val).sum) := by sorry
