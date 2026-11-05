-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_litI_zeroCl
-- name    : CircuitLowerBound.Clause.litI_zeroCl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:49:08.814207+00:00
-- url     : https://prove2.me/theorems/a2547515-f501-4d4c-afaf-9ffd820cd120
-- title:
--   Clause: lit I zero Cl
-- statement:
--   The Clause construction uses the lit I zero Cl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L317-L319
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L317-L319

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

theorem CircuitLowerBound.Clause.litI_zeroCl (ι : ℕ) : litI zeroCl ι = (0, 0, 0, 0, false) := by sorry
