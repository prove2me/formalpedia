-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_two_pow_size_le
-- name    : CircuitLowerBound.TabF.two_pow_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:05:44.811746+00:00
-- url     : https://prove2.me/theorems/4b26ba71-53e7-42c0-b02d-abcaeedaa6da
-- title:
--   Tab F: two pow size le
-- statement:
--   2 to the number of binary digits of n is at most 2n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L182-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L182-L190

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

theorem CircuitLowerBound.TabF.two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by sorry
