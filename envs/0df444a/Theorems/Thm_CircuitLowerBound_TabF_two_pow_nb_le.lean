-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_two_pow_nb_le
-- name    : CircuitLowerBound.TabF.two_pow_nb_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:05:57.047475+00:00
-- url     : https://prove2.me/theorems/3a2449a7-f6f6-4bf1-8bb9-0563d2aa6a2c
-- title:
--   Tab F: two pow nb le
-- statement:
--   Where there is room, the formula of a table has at most (2·(number of clauses of the table) + 1)·2^L
--   clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L212-L218
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L212-L218

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

theorem CircuitLowerBound.TabF.two_pow_nb_le {e : MCode} {L P : ℕ} (hF : Fits e L P) : 2 ^ nb e L ≤ (2 * (tab e).length + 1) * 2 ^ L := by sorry
