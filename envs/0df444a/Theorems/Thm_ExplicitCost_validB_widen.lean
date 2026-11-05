-- Prove2me | Theorems.Thm_ExplicitCost_validB_widen
-- name    : ExplicitCost.validB_widen
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:49:30.982869+00:00
-- url     : https://prove2.me/theorems/bc4052cc-b47f-4360-9e2b-1cc6c939413a
-- title:
--   Explicit Cost: valid B widen
-- statement:
--   The test «all appended bits are 0» is the same on the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L155-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L155-L157

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

theorem ExplicitCost.validB_widen (u : X0 NetInput) : validB (kOf (widen K g u)) (gOf (widen K g u)) askedData.under.toPaperNetwork (widen K g u) = validB K g asked.under.toPaperNetwork u := by sorry
