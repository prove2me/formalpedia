-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_tryAll_iff
-- name    : CircuitLowerBound.TabF.tryAll_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:05:42.926293+00:00
-- url     : https://prove2.me/theorems/03fe7379-c967-48ec-8404-0bf0eeee6789
-- title:
--   Tab F: try All iff
-- statement:
--   What the program decides.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L170-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L170-L171

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

theorem CircuitLowerBound.TabF.tryAll_iff (N : ℕ) (φ : Cnf) : tryAll N φ = true ↔ ∃ α < N, ∀ C ∈ φ, ∃ l ∈ C, α.testBit l.1 = l.2 := by sorry
