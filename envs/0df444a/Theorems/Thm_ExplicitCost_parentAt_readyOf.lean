-- Prove2me | Theorems.Thm_ExplicitCost_parentAt_readyOf
-- name    : ExplicitCost.parentAt_readyOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:10:48.219974+00:00
-- url     : https://prove2.me/theorems/e1a48de9-185d-4e9b-888e-7ca7f6b47d50
-- title:
--   Explicit Cost: parent At ready Of
-- statement:
--   The parent that the solver hands to a callee at the level ℓ + 1: K = K_ℓ, g = g_ℓ, the solver's
--   λ and B, the lists of the pieces for λ, the direction, y and x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L55-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CliqueReads.lean#L55-L62

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

theorem ExplicitCost.parentAt_readyOf (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ} (hl : hLev h = l + 1) (y x : ℕ) :
    parentAt (readyOf D x₀ h, y) x = mkParent D (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (hLam h) (hB h) (direction (readyOf D x₀ h, y)) y x := by sorry
