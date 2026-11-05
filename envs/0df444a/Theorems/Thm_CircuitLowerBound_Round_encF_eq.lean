-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_encF_eq
-- name    : CircuitLowerBound.Round.encF_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:59:00.733293+00:00
-- url     : https://prove2.me/theorems/ed484c6a-959e-4e2c-8b64-99a4081201da
-- title:
--   Round: enc F eq
-- statement:
--   Under a pad that is at least as long as every variable is large, the code is not cut off.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L205-L211
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L205-L211

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

theorem CircuitLowerBound.Round.encF_eq {pad : List Unit} {φ : Cnf} (h : ∀ C ∈ φ, ∀ l ∈ C, l.1 ≤ pad.length) : encF pad φ = encCnf φ := by sorry
