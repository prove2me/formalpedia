-- Prove2me | Theorems.Thm_ExplicitCost_lamAt_le_max
-- name    : ExplicitCost.lamAt_le_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:10.795265+00:00
-- url     : https://prove2.me/theorems/a1cb4b2d-00d9-46b9-b1fe-311f0df41dc2
-- title:
--   Explicit Cost: lam At le max
-- statement:
--   Λ_i is at most the largest label length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L77-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L77-L78

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

theorem ExplicitCost.lamAt_le_max (ρ : ℝ) (c x₀ lam B : ℕ) {i : ℕ} (hi : i ≤ l) : lamAt ρ c x₀ l lam B i ≤ lamMax ρ c x₀ l lam B := by sorry
