-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_offA_ge
-- name    : CircuitLowerBound.Clause.offA_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:52:13.667507+00:00
-- url     : https://prove2.me/theorems/c9a39ccf-4e79-4240-b946-28349d116724
-- title:
--   Clause: off A ge
-- statement:
--   The Clause construction uses the off A ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L412-L412
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L412-L412

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

theorem CircuitLowerBound.Clause.offA_ge (n bq bt rb R nf ι : ℕ) : n + 2 + rb * R + R * (3 * nf) ≤ offA n bq bt rb R nf ι := by sorry
