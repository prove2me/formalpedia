-- Prove2me | Theorems.Thm_ExplicitCost_xi_facts
-- name    : ExplicitCost.xi_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:21:15.091102+00:00
-- url     : https://prove2.me/theorems/95462e3a-9f3c-4b1a-86f8-a49f083a534e
-- title:
--   Explicit Cost: xi facts
-- statement:
--   What is used of g, λ, B: with Ξ = g²(λ + B).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L33-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L33-L46

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

theorem ExplicitCost.xi_facts {g lam B : ℕ} (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) :
    8 ≤ Xi g lam B ∧ g ≤ Xi g lam B ∧ 2 * (g * g) ≤ Xi g lam B ∧ 2 * lam ≤ Xi g lam B ∧ B ≤ Xi g lam B ∧ g * (g * g) * lam ≤ Xi g lam B * Xi g lam B ∧ B * g ≤ Xi g lam B * Xi g lam B := by sorry
