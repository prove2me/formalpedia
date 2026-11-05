-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_G_eq
-- name    : CircuitLowerBound.TabF.G_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:13:45.89706+00:00
-- url     : https://prove2.me/theorems/f3cde533-464c-47c0-84b0-574035a9a3c3
-- title:
--   Tab F: G eq
-- statement:
--   Where there is room and the pad is long enough, the program writes the formula of the table.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L148-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L148-L150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]

theorem CircuitLowerBound.TabF.G_eq {e : MCode} {L P : ℕ} {pad : List Unit} (hF : Fits e L P) (hp : 2 ^ nb e L ≤ pad.length) :
    G ((e, List.replicate L (), P), pad) = tabF e L P := by sorry
