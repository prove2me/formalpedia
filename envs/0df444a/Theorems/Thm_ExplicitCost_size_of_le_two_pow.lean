-- Prove2me | Theorems.Thm_ExplicitCost_size_of_le_two_pow
-- name    : ExplicitCost.size_of_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:09.083862+00:00
-- url     : https://prove2.me/theorems/1d5580ad-55e9-4e6e-98ac-09f66bce524b
-- title:
--   Explicit Cost: size of le two pow
-- statement:
--   A number n ≤ 2^k has size at most k + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L87-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L87-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverRoom
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.size_of_le_two_pow {n k : ℕ} (h : n ≤ 2 ^ k) : size n ≤ k + 2 := by sorry
