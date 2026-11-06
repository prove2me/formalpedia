-- Prove2me | Theorems.Thm_ExplicitCost_isOne_widen
-- name    : ExplicitCost.isOne_widen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:51:26.065887+00:00
-- url     : https://prove2.me/theorems/3005cc4a-0638-456e-97c3-0923500f75b7
-- title:
--   Explicit Cost: is One widen
-- statement:
--   The test «this factor is 1» is the same on the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L126-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L126-L129

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)

theorem ExplicitCost.isOne_widen (u : (X0 NetInput × ℕ) × ℕ) : isOne (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) (widen₂ K g u) = isOne K g u := by sorry
