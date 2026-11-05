-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_mod_four
-- name    : CircuitLowerBound.Clause.mod_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:48:56.886626+00:00
-- url     : https://prove2.me/theorems/fbed0b6c-0ede-4fb2-94f2-ca81b00b94c8
-- title:
--   Clause: mod four
-- statement:
--   A number modulo 4 from its two lowest bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L177-L181
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L177-L181

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

theorem CircuitLowerBound.Clause.mod_four (md : ℕ) : md % 4 = (md.testBit 0).toNat + 2 * (md.testBit 1).toNat := by sorry
