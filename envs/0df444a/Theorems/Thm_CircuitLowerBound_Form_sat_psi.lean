-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_sat_psi
-- name    : CircuitLowerBound.Form.sat_psi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:58:14.657404+00:00
-- url     : https://prove2.me/theorems/0c4b3a19-12dc-4c42-afe5-6ba9a6795cd4
-- title:
--   Form: sat psi
-- statement:
--   The formula is satisfiable if and only if some assignment satisfies the equations of all gates
--   and gives the wire «out» the value 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L320-L334
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L320-L334

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
import Theorems.Thm_Groundwork_PolyT_dedup
attribute [local fun_prop] Groundwork.PolyT.dedup


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form

theorem CircuitLowerBound.Form.sat_psi (n : ℕ) (K : List GateD) (out : ℕ) : Sat (tseitin n K ++ [[(out, true)]]).dedup ↔ ∃ a : ℕ → Bool, GE a n K ∧ a out = true := by sorry
