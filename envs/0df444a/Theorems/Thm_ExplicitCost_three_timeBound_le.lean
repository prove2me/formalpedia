-- Prove2me | Theorems.Thm_ExplicitCost_three_timeBound_le
-- name    : ExplicitCost.three_timeBound_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:21:06.827644+00:00
-- url     : https://prove2.me/theorems/ab410868-e707-4c68-bfe0-4ee203698ee0
-- title:
--   Explicit Cost: three time Bound le
-- statement:
--   Three times the bound for C₀ is at most the bound for C₀ + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L54-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L54-L63

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

theorem ExplicitCost.three_timeBound_le (ρ : ℝ) {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) (C : ℕ) : 3 * timeBound ρ x₀ C l lam B ≤ timeBound ρ x₀ (C + 1) l lam B := by sorry
