-- Prove2me | Theorems.Thm_ExplicitCost_base_room_le
-- name    : ExplicitCost.base_room_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:01:39.75837+00:00
-- url     : https://prove2.me/theorems/384636cd-a7a1-47c4-85fd-cbe2f9ec97f1
-- title:
--   Explicit Cost: base room le
-- statement:
--   The bound on the states: 3X² + 13X + 22 ≤ X⁶ for X = K(λ + B).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Base.lean#L45-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Base.lean#L45-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_Brute
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Base
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed

theorem ExplicitCost.base_room_le {K lam B : ℕ} (hK : 1 ≤ K) (hl : 1 ≤ lam) (hB : 1 ≤ B) :
    3 * (2 * lam + 1 + (2 * B + 1)) + 3 * (K * (K - 1) / 2 * lam) + 2 * (B * K) + 2 * size K + K * (2 * lam + 2) + B + 13 + 1 ≤ (K * (lam + B)) ^ 6 := by sorry
