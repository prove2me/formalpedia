-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_Fw_lt
-- name    : CircuitLowerBound.Clause.Fw_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:48:47.905203+00:00
-- url     : https://prove2.me/theorems/3bea193b-27d1-4dcd-b498-1811f164fe23
-- title:
--   Clause: Fw lt
-- statement:
--   The Clause construction uses the Fw lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L406-L410
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L406-L410

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

theorem CircuitLowerBound.Clause.Fw_lt (n rb R : ℕ) {nf ι f : ℕ} (hι : ι < 3) (hf : f < nf) : Fw n rb R nf ι f < n + 2 + rb * R + R * (3 * nf) := by sorry
