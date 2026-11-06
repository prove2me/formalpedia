-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_roundF_roundInput
-- name    : CircuitLowerBound.Round.roundF_roundInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:59:58.1482+00:00
-- url     : https://prove2.me/theorems/33df5570-ca0a-42b9-a3b3-fc2d139d3e0f
-- title:
--   Round: round F round Input
-- statement:
--   What a round returns on x and at most 2^m answers, with a pad of at least 2^(2m+4) units, m = |x|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L291-L312
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L291-L312

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
variable {G : (MCode × List Unit × ℕ) × List Unit → Cnf} {fb : List Unit → Bool}

theorem CircuitLowerBound.Round.roundF_roundInput (hG : ∀ (e : MCode) (L P : ℕ) (pad : List Unit), Fits e L P → 2 ^ nb e L ≤ pad.length → G ((e, List.replicate L (), P), pad) = tabF e L P)
    (hfb : ∀ m : ℕ, pos m = top (nu m) →
      (fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m))))
    (hV : StVars) (x ans : List Bool) (ha : ans.length ≤ 2 ^ x.length) {pad : List Unit} (hp : 2 ^ (2 * x.length + 4) ≤ pad.length) :
    roundF G fb (roundInput x ans, pad) =
      bif decide (ans.length ≤ ofWord x) then true :: encCnf (Phi x.length ++ units (ans.map (fun b => !b) ++ [false]))
      else [false, !ans.getD (ofWord x) false] := by sorry
