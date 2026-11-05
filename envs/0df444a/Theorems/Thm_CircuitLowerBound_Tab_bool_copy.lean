-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_bool_copy
-- name    : CircuitLowerBound.Tab.bool_copy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:26.513515+00:00
-- url     : https://prove2.me/theorems/b6aa40fb-ac92-44f3-8cdf-335f30b9e498
-- title:
--   Tab: bool copy
-- statement:
--   The Tab construction uses the bool copy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L120-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L120-L121

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Table
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N}
variable (N) [Finite (Case N)] [∀ k, Finite (N.tm.Γ k)]
variable {N}

theorem CircuitLowerBound.Tab.bool_copy {x y z : Bool} : ((x = false ∨ y = false ∨ z = true) ∧ (x = false ∨ y = true ∨ z = false)) ↔ (x = true → y = z) := by sorry
