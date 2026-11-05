-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_litAt_polyT
-- name    : CircuitLowerBound.TabF.litAt_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:05:21.854456+00:00
-- url     : https://prove2.me/theorems/3bdecc3d-96dc-4214-8e45-c1029c756d6b
-- title:
--   Tab F: lit At poly T
-- statement:
--   A literal of the formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L96-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L96-L106

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

theorem CircuitLowerBound.TabF.litAt_polyT {t q : α → ℕ} {l : α → TLit} (ht : PolyT t) (hq : PolyT q) (hlit : PolyT l) :
    PolyT fun x => litAt (e x) (L x) (P x) (t x) (q x) (l x) := by sorry
