-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_tval_polyT
-- name    : CircuitLowerBound.TabF.tval_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:05:14.412412+00:00
-- url     : https://prove2.me/theorems/b060694b-18c0-451f-b2a4-32a796632e09
-- title:
--   Tab F: tval poly T
-- statement:
--   The time of a literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L65-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L65-L71

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

theorem CircuitLowerBound.TabF.tval_polyT {b t mode : α → ℕ} (hb : Unary b) (ht : PolyT t) (hm : PolyT mode) : PolyT fun x => tval (b x) (t x) (mode x) := by sorry
