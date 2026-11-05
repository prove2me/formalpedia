-- Prove2me | Theorems.Thm_ExplicitCost_size_map_fst
-- name    : ExplicitCost.size_map_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:48:33.7885+00:00
-- url     : https://prove2.me/theorems/1ec4e73c-facc-49c4-ac6b-cd82ec2d2241
-- title:
--   Explicit Cost: size map fst
-- statement:
--   A pair grows as its first component does.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L54-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L54-L57

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

theorem ExplicitCost.size_map_fst {α α' β : Type} [HasSize α] [HasSize α'] [HasSize β] {w : α → α'} {d : ℕ} (hw : ∀ a, size (w a) ≤ size a + d) (p : α × β) : size (Prod.map w id p) ≤ size p + d := by sorry
