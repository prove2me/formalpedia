-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_shape_tseitin
-- name    : CircuitLowerBound.Form.shape_tseitin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:54:35.557586+00:00
-- url     : https://prove2.me/theorems/962fb964-df60-495a-a291-1aa8ee7f4ea3
-- title:
--   Form: shape tseitin
-- statement:
--   The clauses have three literals, and their variables are wires.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L194-L202
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L194-L202

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form

theorem CircuitLowerBound.Form.shape_tseitin (n : ℕ) (K : List GateD) (hK : WF n K) : ∀ D ∈ tseitin n K, D.length ≤ 3 ∧ ∀ l ∈ D, l.1 < n + K.length := by sorry
