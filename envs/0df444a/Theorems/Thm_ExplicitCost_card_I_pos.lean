-- Prove2me | Theorems.Thm_ExplicitCost_card_I_pos
-- name    : ExplicitCost.card_I_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:59.407147+00:00
-- url     : https://prove2.me/theorems/5d20269f-5dfd-4884-aa55-38e1ddeae315
-- title:
--   Explicit Cost: card I pos
-- statement:
--   𝓘 is not empty.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L145-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/GridLemmas.lean#L145-L152

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

theorem ExplicitCost.card_I_pos {ρ : ℝ} {c : ℕ} {D : PiecesCounted.Data} (h : D.Is ρ c) {lam : ℕ} (hlam : 1 ≤ lam) : 1 ≤ #(D.fam lam).I := by sorry
