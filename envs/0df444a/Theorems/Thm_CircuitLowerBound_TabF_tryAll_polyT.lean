-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_tryAll_polyT
-- name    : CircuitLowerBound.TabF.tryAll_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:05:50.091208+00:00
-- url     : https://prove2.me/theorems/2651d1ee-d4f0-4ec8-8aa0-6e9a25b2d69b
-- title:
--   Tab F: try All poly T
-- statement:
--   Trying all numbers below a number in unary is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L174-L177
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L174-L177

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]

theorem CircuitLowerBound.TabF.tryAll_polyT {N : α → ℕ} {φ : α → Cnf} (hN : Unary N) (hφ : PolyT φ) : PolyT fun x => tryAll (N x) (φ x) := by sorry
