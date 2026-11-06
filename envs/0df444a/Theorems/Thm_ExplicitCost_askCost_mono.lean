-- Prove2me | Theorems.Thm_ExplicitCost_askCost_mono
-- name    : ExplicitCost.askCost_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:50.027263+00:00
-- url     : https://prove2.me/theorems/10666a43-dc3b-43c8-ae92-1e7b4f3ee268
-- title:
--   Explicit Cost: ask Cost mono
-- statement:
--   The price of a query to the pieces grows with λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L58-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L58-L59

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

theorem ExplicitCost.askCost_mono (c : ℕ) {u u' : ℕ} (h : u ≤ u') : askCost c u ≤ askCost c u' := by sorry
