-- Prove2me | Theorems.Thm_ExplicitCost_size_lt_le
-- name    : ExplicitCost.size_lt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:54:02.570006+00:00
-- url     : https://prove2.me/theorems/d73908c5-0971-4150-a1be-681018bdca53
-- title:
--   Explicit Cost: size lt le
-- statement:
--   A counter below n has size at most the size of n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L39-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L39-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ParentNumbers
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowWeightRun
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.size_lt_le {i n : ℕ} (h : i < n) : size i ≤ size n := by sorry
