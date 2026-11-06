-- Prove2me | Theorems.Thm_ExplicitCost_size_of_abs_lt
-- name    : ExplicitCost.size_of_abs_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:47.4092+00:00
-- url     : https://prove2.me/theorems/a4c6f0a7-f8ce-475f-b89c-6a22b5753976
-- title:
--   Explicit Cost: size of abs lt
-- statement:
--   An integer below 2^m in absolute value has size at most m + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L96-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L96-L100

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

theorem ExplicitCost.size_of_abs_lt {v : ℤ} {m : ℕ} (h : |v| < 2 ^ m) : size v ≤ m + 1 := by sorry
