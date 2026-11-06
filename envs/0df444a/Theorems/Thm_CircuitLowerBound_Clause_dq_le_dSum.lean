-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_dq_le_dSum
-- name    : CircuitLowerBound.Clause.dq_le_dSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:56:18.215612+00:00
-- url     : https://prove2.me/theorems/2d61527b-f33b-47d3-90da-af876b19c0f5
-- title:
--   Clause: dq le d Sum
-- statement:
--   No number that the table adds to a position is larger than `dSum`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L789-L796
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L789-L796

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

theorem CircuitLowerBound.Clause.dq_le_dSum (tb : List TCl) (k ι : ℕ) : (litI (tb.getD k zeroCl) ι).2.2.2.1 ≤ dSum tb := by sorry
