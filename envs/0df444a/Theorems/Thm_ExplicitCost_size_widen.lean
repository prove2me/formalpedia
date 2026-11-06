-- Prove2me | Theorems.Thm_ExplicitCost_size_widen
-- name    : ExplicitCost.size_widen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:48:43.431396+00:00
-- url     : https://prove2.me/theorems/5d2f1387-8e4d-443d-8b00-5cdffe76e2cc
-- title:
--   Explicit Cost: size widen
-- statement:
--   The widened input of the machine is larger by one copy of K and g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L48-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L48-L51

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

theorem ExplicitCost.size_widen (u : X0 NetInput) : size (widen K g u) = size u + (2 * K + 2 * g + 2) := by sorry
