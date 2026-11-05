-- Prove2me | Theorems.Thm_ExplicitCost_size_widenC
-- name    : ExplicitCost.size_widenC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:48:54.96521+00:00
-- url     : https://prove2.me/theorems/c9f00a43-cc4b-4ead-ab44-c7c603802301
-- title:
--   Explicit Cost: size widen C
-- statement:
--   One copy of K and g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L42-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L42-L45

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

theorem ExplicitCost.size_widenC (c : NetInput) : size (widenC K g c) = size c + (2 * K + 2 * g + 2) := by sorry
