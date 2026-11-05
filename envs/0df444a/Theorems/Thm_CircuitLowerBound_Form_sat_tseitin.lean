-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_sat_tseitin
-- name    : CircuitLowerBound.Form.sat_tseitin
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:54:07.155987+00:00
-- url     : https://prove2.me/theorems/c40d1f2e-6338-4a89-93e0-c1df29e16b92
-- title:
--   Form: sat tseitin
-- statement:
--   The Form construction uses the sat tseitin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L180-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L180-L191

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

theorem CircuitLowerBound.Form.sat_tseitin (a : ℕ → Bool) (n : ℕ) (K : List GateD) : (∀ D ∈ tseitin n K, ∃ l ∈ D, a l.1 = l.2) ↔ GE a n K := by sorry
