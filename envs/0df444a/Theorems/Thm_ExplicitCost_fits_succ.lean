-- Prove2me | Theorems.Thm_ExplicitCost_fits_succ
-- name    : ExplicitCost.fits_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:20:19.870887+00:00
-- url     : https://prove2.me/theorems/3d32fe52-f074-412f-ab36-ee72795810a5
-- title:
--   Explicit Cost: fits succ
-- statement:
--   A well-formed instance of the level ℓ + 1: λ, B ≥ 1, the tables read from its oracle are below
--   2^B on the settings of the clique on g_ℓ·g_ℓ nodes, and the oracle is the oracle of these tables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L103-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L103-L113

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.fits_succ {x₀ l : ℕ} {a : Ctx} {f : TableQuery → Option Ans} (hF : Fits x₀ a f) (hl : cLev a = l + 1) :
    1 ≤ cLam a ∧ 1 ≤ cB a ∧ (∀ w < Levels.Gen.g x₀ l * Levels.Gen.g x₀ l, ∀ z ∈ words ((Levels.Gen.g x₀ l * Levels.Gen.g x₀ l - 1) * cLam a), |readTables f w z| < 2 ^ cB a) ∧
      f = answersOf (Levels.Gen.g x₀ l * Levels.Gen.g x₀ l) (cLam a) (readTables f) := by sorry
