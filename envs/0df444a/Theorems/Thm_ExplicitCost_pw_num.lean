-- Prove2me | Theorems.Thm_ExplicitCost_pw_num
-- name    : ExplicitCost.pw_num
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:50.728626+00:00
-- url     : https://prove2.me/theorems/eee99413-24cb-4c1c-bdda-e70fc4abed31
-- title:
--   Explicit Cost: pw num
-- statement:
--   n ≤ X^n for X ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L44-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L44-L44

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

theorem ExplicitCost.pw_num {X : ℕ} (hX : 2 ≤ X) (n : ℕ) : n ≤ X ^ n := by sorry
