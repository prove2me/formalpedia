-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_dWire_lt
-- name    : CircuitLowerBound.Clause.dWire_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:52:30.005224+00:00
-- url     : https://prove2.me/theorems/921d8595-5ebf-448c-ae81-1d29a2f2c417
-- title:
--   Clause: d Wire lt
-- statement:
--   The Clause construction uses the d Wire lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L414-L418
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L414-L418

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

theorem CircuitLowerBound.Clause.dWire_lt (n rb R kbm Dq : ℕ) {ι : ℕ} (hι : ι < 3) (i : ℕ) : dWire n rb R kbm Dq ι i < n + 2 + rb * R + R * (3 * (5 + kbm + Dq)) := by sorry
