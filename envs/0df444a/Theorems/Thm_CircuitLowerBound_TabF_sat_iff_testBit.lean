-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_sat_iff_testBit
-- name    : CircuitLowerBound.TabF.sat_iff_testBit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:05:23.346201+00:00
-- url     : https://prove2.me/theorems/72dbcbf3-cde4-479b-a903-6a14c98c1f2b
-- title:
--   Tab F: sat iff test Bit
-- statement:
--   A formula with variables below M is satisfiable if and only if the binary digits of some number
--   below 2^M satisfy it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L156-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L156-L164

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]

theorem CircuitLowerBound.TabF.sat_iff_testBit (φ : Cnf) (M : ℕ) (hv : ∀ C ∈ φ, ∀ l ∈ C, l.1 < M) :
    Sat φ ↔ ∃ α < 2 ^ M, ∀ C ∈ φ, ∃ l ∈ C, α.testBit l.1 = l.2 := by sorry
