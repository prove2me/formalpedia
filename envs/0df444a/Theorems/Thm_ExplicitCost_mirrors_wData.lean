-- Prove2me | Theorems.Thm_ExplicitCost_mirrors_wData
-- name    : ExplicitCost.mirrors_wData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:51:56.305351+00:00
-- url     : https://prove2.me/theorems/29a3caa2-e5ff-4f08-9669-58ea541b3bc0
-- title:
--   Explicit Cost: mirrors w Data
-- statement:
--   [z_a ∈ S_a]·W_a(z_a): the pending query and the copy beside the test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L162-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L162-L163

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

theorem ExplicitCost.mirrors_wData : Mirrors (wQ K g asked) wData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) := by sorry
