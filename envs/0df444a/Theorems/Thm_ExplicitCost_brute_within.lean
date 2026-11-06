-- Prove2me | Theorems.Thm_ExplicitCost_brute_within
-- name    : ExplicitCost.brute_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:47.138496+00:00
-- url     : https://prove2.me/theorems/77b89439-38e2-404f-9fda-737a02cd0360
-- title:
--   Explicit Cost: brute within
-- statement:
--   Brute force on K nodes, if a query to the tables costs tq operations. The input is (λ, B) in
--   unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Brute.lean#L42-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Brute.lean#L42-L122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Within
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Brute
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed

theorem ExplicitCost.brute_within (K : ℕ) (c : List Unit × List Unit) (W : ℕ → List Bool → ℤ) (hW : ∀ w < K, ∀ z ∈ words ((K - 1) * c.1.length), |W w z| < 2 ^ c.2.length) (tq : ℕ) :
    (bruteMachine K).Within (tables K c.1.length W) (fun _ => tq) c (2 ^ (K * (K - 1) / 2 * c.1.length) * (K * (tq + 1) + 1))
      (3 * size c + 3 * (K * (K - 1) / 2 * c.1.length) + 2 * (c.2.length * K) + 2 * size K + K * (2 * c.1.length + 2) + c.2.length + 13) (clique K c.1.length fun w => W w.val).value := by sorry
