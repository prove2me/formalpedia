-- Prove2me | Theorems.Thm_ExplicitCost_room_term_le
-- name    : ExplicitCost.room_term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:09:59.134575+00:00
-- url     : https://prove2.me/theorems/39ff3eac-6f37-4362-884f-17b57014fb34
-- title:
--   Explicit Cost: room term le
-- statement:
--   A power of K_i(λ' + B'), for λ' and B' within the bounds of the depth i ≤ ℓ, is within the room
--   for all depths.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L69-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L69-L74

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

theorem ExplicitCost.room_term_le (ρ : ℝ) (c x₀ lam B : ℕ) {C C' i u v : ℕ} (hC : C' ≤ C) (hi : i ≤ l) (h1 : 1 ≤ u) (hu : u ≤ lamAt ρ c x₀ l lam B i) (hv : v ≤ bitsAt ρ c x₀ l lam B i) : (Levels.Gen.K x₀ i * (u + v)) ^ C' ≤ roomAll C ρ c x₀ l lam B := by sorry
