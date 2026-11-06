-- Prove2me | Theorems.Thm_ExplicitCost_base_ge
-- name    : ExplicitCost.base_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:03.303019+00:00
-- url     : https://prove2.me/theorems/9fad180e-5adb-4074-afd4-dab6463d8061
-- title:
--   Explicit Cost: base ge
-- statement:
--   X = K_ℓ(λ + B) ≥ 8.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L33-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndBounds.lean#L33-L39

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

theorem ExplicitCost.base_ge {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) : (8 : ℝ) ≤ (Levels.Gen.K x₀ l : ℝ) * ((lam : ℝ) + B) := by sorry
