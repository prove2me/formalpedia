-- Prove2me | Theorems.Thm_ExplicitCost_pow_lt_bitsOne
-- name    : ExplicitCost.pow_lt_bitsOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:33:53.896134+00:00
-- url     : https://prove2.me/theorems/14c9ba4e-215d-4613-b088-a814721534b4
-- title:
--   Explicit Cost: pow lt bits One
-- statement:
--   2^{g²(2λ)^c} is below 2^{B₁}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L43-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L43-L48

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

theorem ExplicitCost.pow_lt_bitsOne (hg : 1 ≤ g) (hB : 1 ≤ B) : (2 : ℤ) ^ (nMemb g g tr * 0 + nMemb g g tr ^ 2 * (2 * lam) ^ c) < 2 ^ bitsOne c g lam B := by sorry
