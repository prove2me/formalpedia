-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_table_of_spec
-- name    : CircuitLowerBound.Tab.table_of_spec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:43:17.154863+00:00
-- url     : https://prove2.me/theorems/9a20bd91-73a8-4f64-b611-c07086db9059
-- title:
--   Tab: table of spec
-- statement:
--   If the conditions hold, all shifts of the clauses of the table hold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L180-L212
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L180-L212

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

theorem CircuitLowerBound.Tab.table_of_spec {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ} (h : Spec N α b Q P) : ∀ c ∈ table N, HoldsC α b Q P c := by sorry
