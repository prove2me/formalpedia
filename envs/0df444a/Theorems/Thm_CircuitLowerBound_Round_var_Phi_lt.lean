-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_var_Phi_lt
-- name    : CircuitLowerBound.Round.var_Phi_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:00:19.19607+00:00
-- url     : https://prove2.me/theorems/630f6ed0-109d-4af1-b8a8-fffdb5b3753f
-- title:
--   Round: var Phi lt
-- statement:
--   The variables of `Phi m` have m bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L245-L254
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L245-L254

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

theorem CircuitLowerBound.Round.var_Phi_lt (hV : StVars) (m : ℕ) : ∀ C ∈ Phi m, ∀ l ∈ C, l.1 < 2 ^ m := by sorry
