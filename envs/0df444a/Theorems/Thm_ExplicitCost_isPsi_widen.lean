-- Prove2me | Theorems.Thm_ExplicitCost_isPsi_widen
-- name    : ExplicitCost.isPsi_widen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:49:27.21355+00:00
-- url     : https://prove2.me/theorems/f6b1261a-0d18-44f1-b9e2-47c14ac59fa8
-- title:
--   Explicit Cost: is Psi widen
-- statement:
--   The test «this factor is a value of Ψ_{a,b}» is the same on the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L138-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L138-L141

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

theorem ExplicitCost.isPsi_widen (u : (X0 NetInput × ℕ) × ℕ) : isPsi (kOf (widen₂ K g u).1.1) (gOf (widen₂ K g u).1.1) (widen₂ K g u) = isPsi K g u := by sorry
