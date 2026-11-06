-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_ex3
-- name    : CircuitLowerBound.Form.ex3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:54:19.378124+00:00
-- url     : https://prove2.me/theorems/ace09801-a7a5-4451-b327-eb67b69c035c
-- title:
--   Form: ex3
-- statement:
--   A clause of three literals is satisfied if one of the three is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L160-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L160-L166

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Form
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form

theorem CircuitLowerBound.Form.ex3 (a : ℕ → Bool) (l1 l2 l3 : ℕ × Bool) : (∃ l ∈ [l1, l2, l3], a l.1 = l.2) ↔ a l1.1 = l1.2 ∨ a l2.1 = l2.2 ∨ a l3.1 = l3.2 := by sorry
