-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_table_dq
-- name    : CircuitLowerBound.Tab.table_dq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:43:17.170581+00:00
-- url     : https://prove2.me/theorems/6e7607aa-79b0-4b8b-b334-443142d2aba6
-- title:
--   Tab: table dq
-- statement:
--   The numbers added to positions are at most 2d.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L215-L224
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean#L215-L224

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

theorem CircuitLowerBound.Tab.table_dq : ∀ c ∈ table N, c.1.2.2.2.1 ≤ 2 * dep N ∧ c.2.1.2.2.2.1 ≤ 2 * dep N ∧ c.2.2.2.2.2.1 ≤ 2 * dep N := by sorry
