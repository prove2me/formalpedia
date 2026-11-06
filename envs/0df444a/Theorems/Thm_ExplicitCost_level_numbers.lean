-- Prove2me | Theorems.Thm_ExplicitCost_level_numbers
-- name    : ExplicitCost.level_numbers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:20:14.045031+00:00
-- url     : https://prove2.me/theorems/0011e3da-9396-4119-8230-19e5aae7307b
-- title:
--   Explicit Cost: level numbers
-- statement:
--   K_ℓ ≥ 2, K_ℓ ≤ g_ℓ, g_ℓ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L33-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L33-L34

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

theorem ExplicitCost.level_numbers {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) : 2 ≤ Levels.Gen.K x₀ l ∧ Levels.Gen.K x₀ l ≤ Levels.Gen.g x₀ l ∧ 2 ≤ Levels.Gen.g x₀ l := by sorry
