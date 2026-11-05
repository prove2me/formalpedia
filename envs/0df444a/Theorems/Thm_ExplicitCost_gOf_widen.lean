-- Prove2me | Theorems.Thm_ExplicitCost_gOf_widen
-- name    : ExplicitCost.gOf_widen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:48:02.548812+00:00
-- url     : https://prove2.me/theorems/5a4fe57b-d695-4e00-a80b-d647596342e0
-- title:
--   Explicit Cost: g Of widen
-- statement:
--   The g that the machine reads off the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L63-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L63-L63

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

theorem ExplicitCost.gOf_widen (u : X0 NetInput) : gOf (widen K g u) = g := by sorry
