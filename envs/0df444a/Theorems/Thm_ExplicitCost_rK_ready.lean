-- Prove2me | Theorems.Thm_ExplicitCost_rK_ready
-- name    : ExplicitCost.rK_ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:03:19.293838+00:00
-- url     : https://prove2.me/theorems/3abb5249-bca0-4c6a-a14a-06c594ca5a92
-- title:
--   Explicit Cost: r K ready
-- statement:
--   The K that the solver holds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L65-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L65-L66

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

theorem ExplicitCost.rK_ready (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ} (hl : hLev h = l + 1) : rK (readyOf D x₀ h) = Levels.Gen.K x₀ l := by sorry
