-- Prove2me | Theorems.Thm_ExplicitCost_qPsi_widen
-- name    : ExplicitCost.qPsi_widen
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:51:53.316659+00:00
-- url     : https://prove2.me/theorems/907cec1e-5aba-4520-8659-351201ac9ae3
-- title:
--   Explicit Cost: q Psi widen
-- statement:
--   The query ((a, b), (z_a, z_b)) is the same on the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L119-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L119-L123

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

theorem ExplicitCost.qPsi_widen (u : (X0 NetInput × ℕ) × ℕ) :
    qPsi (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) askedData.under (widen₂ K g u) = Prod.map (widenC K g) id (qPsi K g asked.under u) := by sorry
