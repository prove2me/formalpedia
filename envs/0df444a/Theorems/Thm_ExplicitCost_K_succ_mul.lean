-- Prove2me | Theorems.Thm_ExplicitCost_K_succ_mul
-- name    : ExplicitCost.K_succ_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:06.379403+00:00
-- url     : https://prove2.me/theorems/a45896ea-ec40-4f18-a36c-adc77b8ec367
-- title:
--   Explicit Cost: K succ mul
-- statement:
--   K_{ℓ+1} = g_ℓ².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L54-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L54-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.K_succ_mul (x₀ l : ℕ) : Levels.Gen.K x₀ (l + 1) = Levels.Gen.g x₀ l * Levels.Gen.g x₀ l := by sorry
