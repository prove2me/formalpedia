-- Prove2me | Theorems.Thm_ExplicitCost_bot_piecesOf
-- name    : ExplicitCost.bot_piecesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:13:43.669993+00:00
-- url     : https://prove2.me/theorems/4d30287f-75af-48bc-b8e6-c843f6842eff
-- title:
--   Explicit Cost: bot pieces Of
-- statement:
--   The function of the second pair of strings, in the form that this development uses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L140-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L140-L142

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

theorem ExplicitCost.bot_piecesOf (D : PiecesCounted.Data) (c : ℕ) {lam : ℕ} (pad : U) (tr : Bool) (j : ℕ) (x y : Pieces.Bits lam) (θ : List Bool) :
    (piecesOf D c).bot ((pad, tr), (0, j), (ClauseBound.Alg.bitsOf x, ClauseBound.Alg.bitsOf y, θ)) = if θ.length = D.cap lam tr (indexAt D lam j) then D.fn lam tr true (indexAt D lam j) (x, y) θ else 0 := by sorry
