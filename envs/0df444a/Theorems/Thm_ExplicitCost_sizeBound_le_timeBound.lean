-- Prove2me | Theorems.Thm_ExplicitCost_sizeBound_le_timeBound
-- name    : ExplicitCost.sizeBound_le_timeBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:17.423206+00:00
-- url     : https://prove2.me/theorems/dcf12fb4-14d6-4d86-829b-8cd16a5ada2a
-- title:
--   Explicit Cost: size Bound le time Bound
-- statement:
--   The bound on the sizes is at most the bound of the theorem: K_ℓ ≤ K_ℓ² and e_ℓ ≥ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L66-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L66-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_Printed_Coding
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndBounds
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.sizeBound_le_timeBound {ρ : ℝ} (hρ : 1 / 2 ≤ ρ) {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) (C : ℕ) : sizeBound x₀ C l lam B ≤ timeBound ρ x₀ C l lam B := by sorry
