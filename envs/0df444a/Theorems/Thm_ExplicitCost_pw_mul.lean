-- Prove2me | Theorems.Thm_ExplicitCost_pw_mul
-- name    : ExplicitCost.pw_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:09.460251+00:00
-- url     : https://prove2.me/theorems/bd506427-a5ed-4f84-bedf-754ddfe2a94f
-- title:
--   Explicit Cost: pw mul
-- statement:
--   A product of two numbers that are at most powers of X.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L39-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L39-L41

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

theorem ExplicitCost.pw_mul {X a b i j : ℕ} (ha : a ≤ X ^ i) (hb : b ≤ X ^ j) : a * b ≤ X ^ (i + j) := by sorry
