-- Prove2me | Theorems.Thm_ExplicitCost_kOf_widen
-- name    : ExplicitCost.kOf_widen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:46:17.882348+00:00
-- url     : https://prove2.me/theorems/713ab2f0-2f37-4a1f-81f1-c0d9e46fe100
-- title:
--   Explicit Cost: k Of widen
-- statement:
--   The K that the machine reads off the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L60-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L60-L60

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

theorem ExplicitCost.kOf_widen (u : X0 NetInput) : kOf (widen K g u) = K := by sorry
