-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_PhiF_eq
-- name    : CircuitLowerBound.Round.PhiF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T22:00:27.506186+00:00
-- url     : https://prove2.me/theorems/b53477e7-f58f-4718-89c3-6e94a97c7068
-- title:
--   Round: Phi F eq
-- statement:
--   With a pad of at least 2^(2m) units, `PhiF` writes `Phi m`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L268-L288
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L268-L288

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Round
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
variable {G : (MCode × List Unit × ℕ) × List Unit → Cnf} {fb : List Unit → Bool}

theorem CircuitLowerBound.Round.PhiF_eq (hG : ∀ (e : MCode) (L P : ℕ) (pad : List Unit), Fits e L P → 2 ^ nb e L ≤ pad.length → G ((e, List.replicate L (), P), pad) = tabF e L P)
    (hfb : ∀ m : ℕ, pos m = top (nu m) →
      (fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m))))
    (m : ℕ) {pad : List Unit} (hp : 2 ^ (2 * m) ≤ pad.length) : PhiF G fb (List.replicate m ()) pad = Phi m := by sorry
