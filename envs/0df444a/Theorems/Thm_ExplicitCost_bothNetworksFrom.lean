-- Prove2me | Theorems.Thm_ExplicitCost_bothNetworksFrom
-- name    : ExplicitCost.bothNetworksFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:22:49.458353+00:00
-- url     : https://prove2.me/theorems/eb1b2fad-11de-4d2e-85df-7c9c8d881905
-- title:
--   Explicit Cost: both Networks From
-- statement:
--   The two networks, assuming that Ψ is the product that `rowPair` computes (used for the run of
--   `rowPair`) and that the numbers read from the lists are those of the pieces (used for the input that
--   the procedure writes and for the runs of `rowPair` and `rowFactor`). What the grid needs of the
--   pieces is taken from `cutsOK_piecesOf`. C₂ = 2c + 6.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L193-L194
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L193-L194

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowFactorRun
import Definitions.Def_CountedRecursion_ParentSize
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_BothNetworks
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.bothNetworksFrom : BothNetworksFrom := by sorry
