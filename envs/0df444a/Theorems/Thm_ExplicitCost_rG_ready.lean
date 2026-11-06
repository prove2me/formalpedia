-- Prove2me | Theorems.Thm_ExplicitCost_rG_ready
-- name    : ExplicitCost.rG_ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:02.71662+00:00
-- url     : https://prove2.me/theorems/0f4dc01b-3e9e-4606-a1e9-7a9b657d2ed6
-- title:
--   Explicit Cost: r G ready
-- statement:
--   The g that the solver holds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L69-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L69-L70

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

theorem ExplicitCost.rG_ready (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ} (hl : hLev h = l + 1) : rG (readyOf D x₀ h) = Levels.Gen.g x₀ l := by sorry
