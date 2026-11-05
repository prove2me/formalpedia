-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_clauseAt_polyT
-- name    : CircuitLowerBound.TabF.clauseAt_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:05:29.328814+00:00
-- url     : https://prove2.me/theorems/f4dbf228-6351-48e6-9e6f-edacbdf89cee
-- title:
--   Tab F: clause At poly T
-- statement:
--   A clause of the formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L109-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L109-L123

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
variable {e : α → MCode} {L P : α → ℕ} (he : PolyT e) (hk : Unary fun x => kb (e x)) (hl : Unary fun x => lam (e x)) (hL : Unary L) (hP : PolyT P)
include he hk hl hL
include hP

theorem CircuitLowerBound.TabF.clauseAt_polyT {j : α → ℕ} (hj : PolyT j) : PolyT fun x => clauseAt (e x) (L x) (P x) (j x) := by sorry
