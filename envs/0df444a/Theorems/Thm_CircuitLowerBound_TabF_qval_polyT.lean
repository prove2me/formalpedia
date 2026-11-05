-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_qval_polyT
-- name    : CircuitLowerBound.TabF.qval_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:04:28.360067+00:00
-- url     : https://prove2.me/theorems/4c5fa8ef-c758-4566-b03d-d6e841f7fe9d
-- title:
--   Tab F: qval poly T
-- statement:
--   The position of a literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L74-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L74-L79

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

theorem CircuitLowerBound.TabF.qval_polyT {P q mode : α → ℕ} (hP : PolyT P) (hq : PolyT q) (hm : PolyT mode) : PolyT fun x => qval (P x) (q x) (mode x) := by sorry
