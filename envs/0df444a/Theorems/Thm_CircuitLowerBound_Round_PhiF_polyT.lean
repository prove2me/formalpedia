-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_PhiF_polyT
-- name    : CircuitLowerBound.Round.PhiF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:01:09.728286+00:00
-- url     : https://prove2.me/theorems/5e1acd85-a49c-42de-be0e-33cb390076ca
-- title:
--   Round: Phi F poly T
-- statement:
--   The Round construction uses the Phi F poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L347-L365
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L347-L365

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
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round
variable {G : (MCode × List Unit × ℕ) × List Unit → Cnf} {fb : List Unit → Bool}
variable {α : Type} [Enc α]

theorem CircuitLowerBound.Round.PhiF_polyT (h1 : StCertSched) (hG : PolyT G) (hfb : PolyT fb) {u pad : α → List Unit} (hu : PolyT u) (hp : PolyT pad) :
    PolyT fun x => PhiF G fb (u x) (pad x) := by sorry
