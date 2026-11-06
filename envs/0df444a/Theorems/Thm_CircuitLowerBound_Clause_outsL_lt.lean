-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_outsL_lt
-- name    : CircuitLowerBound.Clause.outsL_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:52:54.667585+00:00
-- url     : https://prove2.me/theorems/e204fc93-845a-4569-b7a7-94a6afe2d480
-- title:
--   Clause: outs L lt
-- statement:
--   The output wires are wires of the circuit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L452-L470
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L452-L470

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

theorem CircuitLowerBound.Clause.outsL_lt (n bq bt rb R kbm Dq L : ℕ) {ι : ℕ} (hι : ι < 3) :
    ∀ w ∈ outsL n bq bt rb R kbm Dq L ι, w < n + (2 + rb * R + R * (3 * (5 + kbm + Dq)) + szL bq bt * 3) := by sorry
