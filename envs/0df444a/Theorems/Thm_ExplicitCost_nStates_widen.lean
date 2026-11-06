-- Prove2me | Theorems.Thm_ExplicitCost_nStates_widen
-- name    : ExplicitCost.nStates_widen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:52:04.743267+00:00
-- url     : https://prove2.me/theorems/1d51500e-541b-4ba5-b93f-ad7a3af68e53
-- title:
--   Explicit Cost: n States widen
-- statement:
--   The number of terms of an entry is the same on the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L150-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L150-L152

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

theorem ExplicitCost.nStates_widen (u : X0 NetInput) : nStates (kOf (widen K g u)) (gOf (widen K g u)) askedData.under.toPaperNetwork (widen K g u) = nStates K g asked.under.toPaperNetwork u := by sorry
