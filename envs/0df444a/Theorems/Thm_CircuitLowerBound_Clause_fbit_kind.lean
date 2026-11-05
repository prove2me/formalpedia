-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_fbit_kind
-- name    : CircuitLowerBound.Clause.fbit_kind
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:52:26.939598+00:00
-- url     : https://prove2.me/theorems/c2f52cff-93eb-4510-92fa-9bcb8c030632
-- title:
--   Clause: fbit kind
-- statement:
--   The Clause construction uses the fbit kind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L474-L478
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L474-L478

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

theorem CircuitLowerBound.Clause.fbit_kind {kbm i : ℕ} (l : TLit) (h : i < kbm) : fbit kbm l (5 + i) = l.1.testBit i := by sorry
