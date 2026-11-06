-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_length_outsL
-- name    : CircuitLowerBound.Clause.length_outsL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:08:15.71546+00:00
-- url     : https://prove2.me/theorems/2e0b9109-1692-4130-9a20-aca74153cd0a
-- title:
--   Clause: length outs L
-- statement:
--   The Clause construction uses the length outs L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L166-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L166-L168

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem CircuitLowerBound.Clause.length_outsL {bq bt kbm L : ℕ} (hL : bq + bt + 2 + kbm ≤ L) (n rb R Dq ι : ℕ) : (outsL n bq bt rb R kbm Dq L ι).length = L + 1 := by sorry
