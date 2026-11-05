-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_xor_op
-- name    : CircuitLowerBound.Form.xor_op
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:55:21.22889+00:00
-- url     : https://prove2.me/theorems/8e37258a-adcd-4aa0-8db3-c721f08a7dd0
-- title:
--   Form: xor op
-- statement:
--   The Form construction uses the xor op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L279-L280
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L279-L280

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

theorem CircuitLowerBound.Form.xor_op (i j : ℕ) (x y : Bool) : (GateD.toGate (xorT, i, j)).op x y = (x != y) := by sorry
