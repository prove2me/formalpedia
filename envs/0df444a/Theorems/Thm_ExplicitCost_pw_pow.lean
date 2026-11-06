-- Prove2me | Theorems.Thm_ExplicitCost_pw_pow
-- name    : ExplicitCost.pw_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:17.733791+00:00
-- url     : https://prove2.me/theorems/e61c4fd0-5d09-42e3-9151-86b0a9363941
-- title:
--   Explicit Cost: pw pow
-- statement:
--   A power of a number that is at most a power of X.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L47-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L47-L49

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

theorem ExplicitCost.pw_pow {X a i : ℕ} (ha : a ≤ X ^ i) (k : ℕ) : a ^ k ≤ X ^ (i * k) := by sorry
