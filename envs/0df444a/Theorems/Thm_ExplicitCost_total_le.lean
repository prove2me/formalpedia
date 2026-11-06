-- Prove2me | Theorems.Thm_ExplicitCost_total_le
-- name    : ExplicitCost.total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:30:09.156535+00:00
-- url     : https://prove2.me/theorems/629ed033-4d0e-4bf5-a2d4-633e19c857f0
-- title:
--   Explicit Cost: total le
-- statement:
--   U ≤ N = g⁴λ, for either network of a pattern.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LabelCrude.lean#L32-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LabelCrude.lean#L32-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CaseTwo
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LabelCrude
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.total_le {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) (g : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ) :
    (patternNet D c g tr lam y W).U ≤ g ^ 4 * lam := by sorry
