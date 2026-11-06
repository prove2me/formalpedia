-- Prove2me | Theorems.Thm_ExplicitCost_nPatterns_ready
-- name    : ExplicitCost.nPatterns_ready
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:55:54.509769+00:00
-- url     : https://prove2.me/theorems/0d2ba082-a910-4d10-ab29-86aecd015649
-- title:
--   Explicit Cost: n Patterns ready
-- statement:
--   The number of patterns: |𝓘|^{|ℛ|}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L73-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L73-L76

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

theorem ExplicitCost.nPatterns_ready (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ} (hl : hLev h = l + 1) :
    nPatterns (readyOf D x₀ h) = #(D.fam (hLam h)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := by sorry
