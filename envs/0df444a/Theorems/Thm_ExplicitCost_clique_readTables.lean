-- Prove2me | Theorems.Thm_ExplicitCost_clique_readTables
-- name    : ExplicitCost.clique_readTables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:04.291886+00:00
-- url     : https://prove2.me/theorems/26f73b1a-1077-41a7-a032-14288515d2d0
-- title:
--   Explicit Cost: clique read Tables
-- statement:
--   So they give the same value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L41-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Definitions.Def_ClauseBound_Alg_Level
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CliqueReads
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.clique_readTables (K lam : ℕ) (W : ℕ → List Bool → ℤ) : (clique K lam fun w => readTables (answersOf K lam W) w.val).value = (clique K lam fun w => W w.val).value := by sorry
