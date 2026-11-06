-- Prove2me | Theorems.Thm_ExplicitCost_fn_bitsOf
-- name    : ExplicitCost.fn_bitsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:14:11.418499+00:00
-- url     : https://prove2.me/theorems/52ce2ece-648c-4fd7-a3d7-21dbb2da4e43
-- title:
--   Explicit Cost: fn bits Of
-- statement:
--   The functions of a factorization, called with strings written as lists.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L123-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L123-L132

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SquareGrid
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_GridLemmas
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.fn_bitsOf (D : PiecesCounted.Data) {lam : ℕ} (tr side : Bool) (j : ℕ) (x y : Pieces.Bits lam) (θ : List Bool) :
    (if θ.length = D.cap (ClauseBound.Alg.bitsOf x).length tr (indexAt D (ClauseBound.Alg.bitsOf x).length j) then
      D.fn (ClauseBound.Alg.bitsOf x).length tr side (indexAt D (ClauseBound.Alg.bitsOf x).length j) (PiecesCounted.toBits _ (ClauseBound.Alg.bitsOf x), PiecesCounted.toBits _ (ClauseBound.Alg.bitsOf y)) θ else 0) =
      if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr side (indexAt D lam j) (x, y) θ else 0 := by sorry
