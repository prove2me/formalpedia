-- Prove2me | Theorems.Thm_CountKSatRate_Top_iterate_le_sum
-- name    : CountKSatRate.Top.iterate_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:14:45.380728+00:00
-- url     : https://prove2.me/theorems/7548c804-e726-4f17-b144-586ea34093ac
-- title:
--   Top: iterate le sum
-- statement:
--   The number after any number of rounds is at most the sum of the values of the leaves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Top.lean#L48-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Top.lean#L48-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Top
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Top
open Finset Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F
open Groundwork.Sparsify (PFml leaves round)
open WidthK (theta bsum leafC)

theorem CountKSatRate.Top.iterate_le_sum (hE : StRoundSEnd) {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ)
    (hd : ∀ x ∈ leaves step d s, step x = none) (i : ℕ) : ((roundS step val)^[i] ([s], 0)).2 ≤ ((leaves step d s).map val).sum := by sorry
