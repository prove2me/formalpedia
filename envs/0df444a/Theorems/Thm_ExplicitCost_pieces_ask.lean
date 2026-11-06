-- Prove2me | Theorems.Thm_ExplicitCost_pieces_ask
-- name    : ExplicitCost.pieces_ask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:15:16.710933+00:00
-- url     : https://prove2.me/theorems/4394ca6e-ec85-4879-98b2-927f61c56e7a
-- title:
--   Explicit Cost: pieces ask
-- statement:
--   The oracle of the pieces, asked about strings of λ bits, 1 ≤ λ ≤ Λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStep.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStep.lean#L32-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverRoom
import Definitions.Def_CountedRecursion_GridLemmas
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStep
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.pieces_ask (D : PiecesCounted.Data) {Lam : ℕ} {u : List Unit} (h1 : 1 ≤ u.length) (h2 : u.length ≤ Lam) (q : PiecesCounted.Question) : piecesUpTo D Lam (u, q) = D.answer u.length q := by sorry
