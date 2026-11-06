-- Prove2me | Theorems.Thm_ExplicitCost_bothNetworks
-- name    : ExplicitCost.bothNetworks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:21:17.701288+00:00
-- url     : https://prove2.me/theorems/4b9eb3c2-e267-4dfc-8b9a-05f0b935edcc
-- title:
--   Explicit Cost: both Networks
-- statement:
--   **«Definition 2 holds with B₁ = gB + g²(2λ)^c in the role of B and with τ = 2^{cλ}Ξ^{C₂}.»**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L197-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/BothNetworks.lean#L197-L197

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
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.bothNetworks : BothNetworks := by sorry
