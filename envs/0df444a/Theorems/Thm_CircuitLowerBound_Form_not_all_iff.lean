-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_not_all_iff
-- name    : CircuitLowerBound.Form.not_all_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:58:56.305061+00:00
-- url     : https://prove2.me/theorems/b61de90b-06ea-48da-9927-01876fce151a
-- title:
--   Form: not all iff
-- statement:
--   Not all clauses of the formula of a table are satisfied: some clause is violated.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L343-L354
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L343-L354

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

theorem CircuitLowerBound.Form.not_all_iff (e : MCode) (L P : ℕ) (f : ℕ → Bool) :
    (¬∀ D ∈ tabF e L P, ∃ l ∈ D, f l.1 = l.2) ↔ ∃ j < 2 ^ nb e L, ∀ l ∈ clauseAt e L P j, f l.1 ≠ l.2 := by sorry
