-- Prove2me | Theorems.Thm_ExplicitCost_lamAt_step
-- name    : ExplicitCost.lamAt_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:09:31.812268+00:00
-- url     : https://prove2.me/theorems/1466e491-5a2d-40a9-9525-cec4f218e0e3
-- title:
--   Explicit Cost: lam At step
-- statement:
--   Λ_j from Λ_{j+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L33-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L33-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Meets
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

theorem ExplicitCost.lamAt_step (ρ : ℝ) (c x₀ lam B : ℕ) (h : j < l) : lamAt ρ c x₀ l lam B j =
    ⌊((ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * lamAt ρ c x₀ l lam B (j + 1)) + (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) + (Levels.Gen.K x₀ j : ℝ) ^ 2) / (Levels.Gen.K x₀ j : ℝ) ^ 2⌋₊ := by sorry
