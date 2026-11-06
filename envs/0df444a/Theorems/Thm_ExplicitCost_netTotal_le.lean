-- Prove2me | Theorems.Thm_ExplicitCost_netTotal_le
-- name    : ExplicitCost.netTotal_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:26:54.980224+00:00
-- url     : https://prove2.me/theorems/c963021b-6c1c-40f3-8d91-0b8d16ca2657
-- title:
--   Explicit Cost: net Total le
-- statement:
--   U ≤ gP, by (i) of Definition 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L68-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L68-L71

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

theorem ExplicitCost.netTotal_le {n : ℕ} (N : Net n) {P B : ℕ} (hN : N.Is P B) : N.U ≤ n * P := by sorry
