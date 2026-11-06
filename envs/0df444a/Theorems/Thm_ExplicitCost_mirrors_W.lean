-- Prove2me | Theorems.Thm_ExplicitCost_mirrors_W
-- name    : ExplicitCost.mirrors_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:49:28.077816+00:00
-- url     : https://prove2.me/theorems/7a427766-5336-43ad-a7c8-cfe2fbb03624
-- title:
--   Explicit Cost: mirrors W
-- statement:
--   W_a(z): one query, the same with K and g beside the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L72-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L72-L73

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

theorem ExplicitCost.mirrors_W : Mirrors asked.W askedData.W (Prod.map (widenC K g) id) (2 * K + 2 * g + 2) := by sorry
