-- Prove2me | Theorems.Thm_ExplicitCost_length_factorChunk
-- name    : ExplicitCost.length_factorChunk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:11:26.802864+00:00
-- url     : https://prove2.me/theorems/46a5cba1-38fc-44a6-b25b-975a731d11aa
-- title:
--   Explicit Cost: length factor Chunk
-- statement:
--   The chunk of a rectangle has as many bits as its piece asks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L66-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L66-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowPairRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowFactorRun
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.length_factorChunk {q : FQ} (hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2) {j : ℕ} (hlt : j / g < j % g) (hg : 0 < g) :
    (factorChunk D c g tr lam y q j).length = D.cap lam tr (indexAt D lam (factorDigit D c g tr lam y q j)) := by sorry
