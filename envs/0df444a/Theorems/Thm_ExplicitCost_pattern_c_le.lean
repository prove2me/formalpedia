-- Prove2me | Theorems.Thm_ExplicitCost_pattern_c_le
-- name    : ExplicitCost.pattern_c_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:33:42.811441+00:00
-- url     : https://prove2.me/theorems/e8d0e006-18d9-4f68-912a-0f33bb3df9a4
-- title:
--   Explicit Cost: pattern c le
-- statement:
--   «c_{a,a'} ≤ g²λ».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L32-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L32-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.pattern_c_le (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (a b : Fin (nParts g g tr)) : (patternNet D c g tr lam y W).c a b ≤ g ^ 2 * lam := by sorry
