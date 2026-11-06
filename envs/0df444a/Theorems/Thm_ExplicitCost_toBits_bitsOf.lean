-- Prove2me | Theorems.Thm_ExplicitCost_toBits_bitsOf
-- name    : ExplicitCost.toBits_bitsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:14:45.716496+00:00
-- url     : https://prove2.me/theorems/6f9f6e31-bee6-426e-8ac2-8843033fe5e5
-- title:
--   Explicit Cost: to Bits bits Of
-- statement:
--   A string written as a list and read again.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L117-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L117-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.toBits_bitsOf {n : ℕ} (x : Pieces.Bits n) : PiecesCounted.toBits n (ClauseBound.Alg.bitsOf x) = x := by sorry
