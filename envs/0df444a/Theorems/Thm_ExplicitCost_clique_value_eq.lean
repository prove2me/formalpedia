-- Prove2me | Theorems.Thm_ExplicitCost_clique_value_eq
-- name    : ExplicitCost.clique_value_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:59:53.468437+00:00
-- url     : https://prove2.me/theorems/e7fb34cb-c548-4dc5-a7c0-2ca5b8b5b45c
-- title:
--   Explicit Cost: clique value eq
-- statement:
--   The value of the clique as the network of Definition 3 is the sum over one string per edge, for
--   every K and λ. By `Value.stCliqueValue`, which has no condition on K and λ. (`Printed.stCliqueValue`
--   says the same for K ≥ 2 and λ ≥ 1.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Brute.lean#L32-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Brute.lean#L32-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Within
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Brute
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed

theorem ExplicitCost.clique_value_eq (K lam : ℕ) (W : ℕ → List Bool → ℤ) : (clique K lam fun w => W w.val).value = Paper.cliqueValue lam (listTables K W) := by sorry
