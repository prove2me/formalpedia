-- Prove2me | Theorems.Thm_ExplicitCost_cost_le
-- name    : ExplicitCost.cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:21:48.835255+00:00
-- url     : https://prove2.me/theorems/48448b7e-c26b-4ee1-8afb-db12c8109933
-- title:
--   Explicit Cost: cost le
-- statement:
--   The costs of the four procedures are at most (2^{cλ} + 2 + tq)·Ξ^{C₂}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L49-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L49-L62

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

theorem ExplicitCost.cost_le {c g lam B tq T : ℕ} (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hT : T ≤ g * g * (askCost c lam + 1) ∨ T ≤ g * (tq + 1) ∨ T ≤ 1) : T ≤ (askCost c lam + tq) * Xi g lam B ^ (2 * c + 6) := by sorry
