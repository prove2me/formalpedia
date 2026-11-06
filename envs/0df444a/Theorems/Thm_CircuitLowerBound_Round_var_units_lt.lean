-- Prove2me | Theorems.Thm_CircuitLowerBound_Round_var_units_lt
-- name    : CircuitLowerBound.Round.var_units_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:00:14.940424+00:00
-- url     : https://prove2.me/theorems/341b145f-0d91-426d-8fe9-700ea9997e9c
-- title:
--   Round: var units lt
-- statement:
--   The variables of `units w` are below the length of w.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L257-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Round.lean#L257-L261

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

theorem CircuitLowerBound.Round.var_units_lt (w : List Bool) : ∀ C ∈ units w, ∀ l ∈ C, l.1 < w.length := by sorry
