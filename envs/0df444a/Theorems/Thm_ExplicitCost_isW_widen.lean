-- Prove2me | Theorems.Thm_ExplicitCost_isW_widen
-- name    : ExplicitCost.isW_widen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:54:20.635577+00:00
-- url     : https://prove2.me/theorems/9561adbf-7814-4dfe-9570-e1e3a9fd86a6
-- title:
--   Explicit Cost: is W widen
-- statement:
--   The test «this factor is a value of W_a» is the same on the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L132-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L132-L135

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

theorem ExplicitCost.isW_widen (u : (X0 NetInput × ℕ) × ℕ) : isW (gOf (widen₂ K g u).1.1) (widen₂ K g u) = isW g u := by sorry
