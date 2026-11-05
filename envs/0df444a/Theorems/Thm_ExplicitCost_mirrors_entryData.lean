-- Prove2me | Theorems.Thm_ExplicitCost_mirrors_entryData
-- name    : ExplicitCost.mirrors_entryData
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:48:24.936669+00:00
-- url     : https://prove2.me/theorems/b246eeea-2ffd-46de-bdfc-b7e510d12a20
-- title:
--   Explicit Cost: mirrors entry Data
-- statement:
--   **One entry**: four copies of K and g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L182-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L182-L187

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

theorem ExplicitCost.mirrors_entryData : Mirrors (tableQ K g asked) entryData (widen K g) (4 * (2 * K + 2 * g + 2)) := by sorry
