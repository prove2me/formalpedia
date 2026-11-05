-- Prove2me | Theorems.Thm_CountKSat_walkSum_runs
-- name    : CountKSat.walkSum_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:52:11.417645+00:00
-- url     : https://prove2.me/theorems/1e0f9850-a4df-4a87-96bc-5b6cb03a04a0
-- title:
--   Count KSat: walk Sum runs
-- statement:
--   If T takes t steps on each leaf and the sum over the leaves is below 2^B, the summing walk takes
--   t + 2 steps per leaf and returns that sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L73-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L73-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Poly_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_Walk
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.Stepped Groundwork.Sparsify
variable {α ν : Type}
open Walk

theorem CountKSat.walkSum_runs [HasSize ν] (step : ν → Option (ν × ν)) {root : α → ν} {T : Stepped ν ℕ} (d : ℕ) (a : α)
    (hd : ∀ x ∈ leaves step d (root a), step x = none) (v : ν → ℕ) (t Sm Sx B : ℕ)
    (hT : ∀ x ∈ leaves step d (root a), T.Runs x t Sm (v x))
    (hS : ∀ i, size ((Sparsify.round step)^[i] ([root a], [])).1 ≤ Sx)
    (hB : ((leaves step d (root a)).map v).sum < 2 ^ B) :
    (walkSum step root T).Runs a ((leaves step d (root a)).length * (t + 2)) (Sx + (B + 1 + (Sm + 1)) + 1)
      ((leaves step d (root a)).map v).sum := by sorry
