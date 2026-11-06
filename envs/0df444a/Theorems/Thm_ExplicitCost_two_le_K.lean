-- Prove2me | Theorems.Thm_ExplicitCost_two_le_K
-- name    : ExplicitCost.two_le_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:01.178196+00:00
-- url     : https://prove2.me/theorems/1a1c927e-836a-420f-a94c-5aa7588c85c5
-- title:
--   Explicit Cost: two le K
-- statement:
--   K_ℓ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L60-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L60-L62

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

theorem ExplicitCost.two_le_K {x₀ : ℕ} (hx : 1 ≤ x₀) (l : ℕ) : 2 ≤ Levels.Gen.K x₀ l := by sorry
