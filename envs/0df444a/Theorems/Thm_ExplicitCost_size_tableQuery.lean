-- Prove2me | Theorems.Thm_ExplicitCost_size_tableQuery
-- name    : ExplicitCost.size_tableQuery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:34.861515+00:00
-- url     : https://prove2.me/theorems/d5e08873-e3ff-4e5e-836c-369cb4dd8210
-- title:
--   Explicit Cost: size table Query
-- statement:
--   A query to the tables that is answered, with its answer, has size at most K + 2Kλ + B + 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L77-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L77-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_Printed_Coding
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndBounds
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.size_tableQuery {K lam B : ℕ} {W : ℕ → List Bool → ℤ} (hW : ∀ w < K, ∀ z ∈ words ((K - 1) * lam), |W w z| < 2 ^ B) {x : TableQuery} {v : Ans} (h : answersOf K lam W x = some v) :
    size x + size v ≤ K + 2 * K * lam + B + 3 := by sorry
