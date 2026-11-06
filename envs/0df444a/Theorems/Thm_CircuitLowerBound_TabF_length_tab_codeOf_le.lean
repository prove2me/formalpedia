-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_length_tab_codeOf_le
-- name    : CircuitLowerBound.TabF.length_tab_codeOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:06:48.148804+00:00
-- url     : https://prove2.me/theorems/5020724b-930b-46f3-9b72-52753c738d7f
-- title:
--   Tab F: length tab code Of le
-- statement:
--   The table with the number a has at most a clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L200-L208
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L200-L208

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

theorem CircuitLowerBound.TabF.length_tab_codeOf_le (a : ℕ) : (tab (codeOf a)).length ≤ a := by sorry
