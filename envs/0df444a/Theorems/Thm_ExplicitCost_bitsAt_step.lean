-- Prove2me | Theorems.Thm_ExplicitCost_bitsAt_step
-- name    : ExplicitCost.bitsAt_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:29.822561+00:00
-- url     : https://prove2.me/theorems/1763c592-910b-40ae-91ed-0fe3fa298f12
-- title:
--   Explicit Cost: bits At step
-- statement:
--   𝔅_j from Λ_{j+1} and 𝔅_{j+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L42-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L42-L47

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

theorem ExplicitCost.bitsAt_step (ρ : ℝ) (c x₀ lam B : ℕ) (h : j < l) : bitsAt ρ c x₀ l lam B j = bitsOut (Levels.Gen.K x₀ j) (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1)) (bitsOne c (Levels.Gen.g x₀ j) (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1))) := by sorry
