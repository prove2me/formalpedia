-- Prove2me | Theorems.Thm_CountKSat_sum_leaves
-- name    : CountKSat.sum_leaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:44:01.476089+00:00
-- url     : https://prove2.me/theorems/8a583b04-fccb-407c-8b5a-01953f9e9fc7
-- title:
--   Count KSat: sum leaves
-- statement:
--   A quantity that is the sum of its values at the two children, at every node with the invariant
--   G, is the sum of its values at the leaves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L55-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L55-L69

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
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.Stepped Groundwork.Sparsify
variable {α ν : Type}
open Walk

theorem CountKSat.sum_leaves {σ : Type*} {step : σ → Option (σ × σ)} {G : σ → ℕ → ℕ → Prop} {q : ℕ}
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q)) (f : σ → ℕ)
    (hf : ∀ s p t l h, G s p t → step s = some (l, h) → f s = f l + f h)
    (d : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : f s = ((leaves step d s).map f).sum := by sorry
