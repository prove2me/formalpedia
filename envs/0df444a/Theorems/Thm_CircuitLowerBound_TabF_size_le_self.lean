-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_size_le_self
-- name    : CircuitLowerBound.TabF.size_le_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:13:32.639807+00:00
-- url     : https://prove2.me/theorems/96a357be-165c-4d99-941a-71e7a5cb566e
-- title:
--   Tab F: size le self
-- statement:
--   A number has at most as many binary digits as its value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L58-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L58-L58

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

theorem CircuitLowerBound.TabF.size_le_self (n : ℕ) : Nat.size n ≤ n := by sorry
