-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_sat_gateCl
-- name    : CircuitLowerBound.Form.sat_gateCl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:53:51.165258+00:00
-- url     : https://prove2.me/theorems/ba19d3b6-0989-4282-8c40-86be61c584dc
-- title:
--   Form: sat gate Cl
-- statement:
--   The Form construction uses the sat gate Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L168-L172
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L168-L172

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

theorem CircuitLowerBound.Form.sat_gateCl (a : ℕ → Bool) (i : ℕ) (g : GateD) :
    (∀ D ∈ gateCl i g, ∃ l ∈ D, a l.1 = l.2) ↔ a i = g.toGate.op (a g.2.1) (a g.2.2) := by sorry
