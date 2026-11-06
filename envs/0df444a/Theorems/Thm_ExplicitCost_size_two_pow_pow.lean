-- Prove2me | Theorems.Thm_ExplicitCost_size_two_pow_pow
-- name    : ExplicitCost.size_two_pow_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:48:55.672174+00:00
-- url     : https://prove2.me/theorems/71413568-97a8-45dd-8e54-8dd41f49c2f9
-- title:
--   Explicit Cost: size two pow pow
-- statement:
--   The size of (2^n)^k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L44-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L44-L45

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

theorem ExplicitCost.size_two_pow_pow (n k : ℕ) : size ((2 ^ n) ^ k) = n * k + 2 := by sorry
