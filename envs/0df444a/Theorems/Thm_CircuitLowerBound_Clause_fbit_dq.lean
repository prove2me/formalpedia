-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_fbit_dq
-- name    : CircuitLowerBound.Clause.fbit_dq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:53:21.703544+00:00
-- url     : https://prove2.me/theorems/51bf29a6-b844-4861-87cf-e0f4b6623240
-- title:
--   Clause: fbit dq
-- statement:
--   The Clause construction uses the fbit dq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L480-L484
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L480-L484

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem CircuitLowerBound.Clause.fbit_dq (kbm i : ℕ) (l : TLit) : fbit kbm l (5 + kbm + i) = l.2.2.2.1.testBit i := by sorry
