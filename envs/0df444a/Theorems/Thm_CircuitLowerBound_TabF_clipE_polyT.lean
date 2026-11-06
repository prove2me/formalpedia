-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_clipE_polyT
-- name    : CircuitLowerBound.TabF.clipE_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:04:36.814011+00:00
-- url     : https://prove2.me/theorems/b2825c31-12fc-4449-be10-5994db249727
-- title:
--   Tab F: clip E poly T
-- statement:
--   The table, cut off, is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L44-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L44-L45

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

theorem CircuitLowerBound.TabF.clipE_polyT {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : PolyT L) : PolyT fun x => clipE (e x) (L x) := by sorry
