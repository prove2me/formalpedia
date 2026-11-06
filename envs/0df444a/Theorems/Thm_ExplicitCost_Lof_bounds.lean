-- Prove2me | Theorems.Thm_ExplicitCost_Lof_bounds
-- name    : ExplicitCost.Lof_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:28:01.76821+00:00
-- url     : https://prove2.me/theorems/c6d902bb-c199-49a2-a25d-55802f64a541
-- title:
--   Explicit Cost: Lof bounds
-- statement:
--   1 ≤ L ≤ gP, for ζ = 1/b, K ≥ 2 and U ≤ gP.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L74-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L74-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallLemma
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.Lof_bounds {K g P U b : ℕ} (hK : 2 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hb : 1 ≤ b) (hU : U ≤ g * P) : 1 ≤ AppRunningTime.Lof K g ((1 : ℝ) / b) P U ∧ AppRunningTime.Lof K g ((1 : ℝ) / b) P U ≤ g * P := by sorry
