-- Prove2me | Theorems.Thm_ExplicitCost_mirrors_mem
-- name    : ExplicitCost.mirrors_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:49:19.675191+00:00
-- url     : https://prove2.me/theorems/0baffaae-8ccc-4777-be73-f9f6c736721c
-- title:
--   Explicit Cost: mirrors mem
-- statement:
--   «Is z ∈ S_a?»: one query, the same with K and g beside the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L68-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L68-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)

theorem ExplicitCost.mirrors_mem : Mirrors asked.mem askedData.mem (Prod.map (widenC K g) id) (2 * K + 2 * g + 2) := by sorry
