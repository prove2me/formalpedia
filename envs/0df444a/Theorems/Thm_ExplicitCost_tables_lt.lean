-- Prove2me | Theorems.Thm_ExplicitCost_tables_lt
-- name    : ExplicitCost.tables_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:58.017665+00:00
-- url     : https://prove2.me/theorems/a5203580-0b6e-4da0-ab71-db631925505c
-- title:
--   Explicit Cost: tables lt
-- statement:
--   The tables of a well-formed instance of the level ℓ + 1, read back from the oracle: |W_w| < 2^B
--   on the g² nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L80-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L80-L86

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

theorem ExplicitCost.tables_lt {x₀ l : ℕ} {a : Ctx} {f : TableQuery → Option Ans} (hF : Fits x₀ a f) (hl : cLev a = l + 1) :
    ∀ w < Levels.Gen.g x₀ l * Levels.Gen.g x₀ l, ∀ z ∈ words ((Levels.Gen.g x₀ l * Levels.Gen.g x₀ l - 1) * cLam a), |readTables f w z| < 2 ^ cB a := by sorry
