-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_clipE_eq
-- name    : CircuitLowerBound.TabF.clipE_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:04:20.489433+00:00
-- url     : https://prove2.me/theorems/61122eb4-f1ec-4340-8207-93fd661322ba
-- title:
--   Tab F: clip E eq
-- statement:
--   Where there is room, the cut-off changes nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L37-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L37-L41

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

theorem CircuitLowerBound.TabF.clipE_eq {e : MCode} {L P : ℕ} (h : Fits e L P) : clipE e L = e := by sorry
