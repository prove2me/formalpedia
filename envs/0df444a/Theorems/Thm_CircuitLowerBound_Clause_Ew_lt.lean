-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_Ew_lt
-- name    : CircuitLowerBound.Clause.Ew_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:52:50.804971+00:00
-- url     : https://prove2.me/theorems/9ed4a33b-f28a-45b0-b13a-c31c11e6d21d
-- title:
--   Clause: Ew lt
-- statement:
--   The Clause construction uses the Ew lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L392-L396
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L392-L396

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem CircuitLowerBound.Clause.Ew_lt (n rb : ℕ) {R k : ℕ} (hk : k < R) : Ew n rb k < n + 2 + rb * R := by sorry
