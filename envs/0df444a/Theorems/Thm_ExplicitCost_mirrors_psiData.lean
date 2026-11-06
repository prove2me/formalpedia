-- Prove2me | Theorems.Thm_ExplicitCost_mirrors_psiData
-- name    : ExplicitCost.mirrors_psiData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:52:16.13624+00:00
-- url     : https://prove2.me/theorems/20bc5bea-b444-4b21-9bcd-e7b2ea119b8f
-- title:
--   Explicit Cost: mirrors psi Data
-- statement:
--   [z_a ∈ S_a][z_b ∈ S_b]·Ψ_{a,b}(z_a, z_b). When the second test begins the copy beside the first
--   is gone.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L167-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L167-L170

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

theorem ExplicitCost.mirrors_psiData : Mirrors (psiQ K g asked) psiData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) := by sorry
