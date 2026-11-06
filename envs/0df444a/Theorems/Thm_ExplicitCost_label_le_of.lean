-- Prove2me | Theorems.Thm_ExplicitCost_label_le_of
-- name    : ExplicitCost.label_le_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:31:56.5832+00:00
-- url     : https://prove2.me/theorems/8c0f6f73-ff70-4897-a2b0-b844cc5d30ee
-- title:
--   Explicit Cost: label le of
-- statement:
--   «L ≤ N + 1», for every U ≤ N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LabelCrude.lean#L46-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LabelCrude.lean#L46-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CaseTwo
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LabelCrude
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.label_le_of (x₀ l lam U : ℕ) (hx : 18 ≤ x₀) (hU : U ≤ Levels.Gen.g x₀ l ^ 4 * lam) :
    AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) U ≤ Levels.Gen.g x₀ l ^ 4 * lam + 1 := by sorry
