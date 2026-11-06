-- Prove2me | Theorems.Thm_ExplicitCost_qF_widen
-- name    : ExplicitCost.qF_widen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:51:09.568869+00:00
-- url     : https://prove2.me/theorems/dc82923b-0705-4d2f-b27e-0dd479e43a81
-- title:
--   Explicit Cost: q F widen
-- statement:
--   The query ((a, b), (z_a, θ_{a,b})) is the same on the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L105-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L105-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)

theorem ExplicitCost.qF_widen (u : (X0 NetInput × ℕ) × ℕ) :
    qF (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) askedData.under.toPaperNetwork (widen₂ K g u) = Prod.map (widenC K g) id (qF K g asked.under.toPaperNetwork u) := by sorry
