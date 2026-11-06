-- Prove2me | Theorems.Thm_ExplicitCost_mirrors_termData
-- name    : ExplicitCost.mirrors_termData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:53:01.095491+00:00
-- url     : https://prove2.me/theorems/08c8da61-b0ac-4c22-8d11-4f81078345ba
-- title:
--   Explicit Cost: mirrors term Data
-- statement:
--   One factor.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L177-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L177-L179

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

theorem ExplicitCost.mirrors_termData : Mirrors (termQ K g asked) termData (widen₂ K g) (2 * (2 * K + 2 * g + 2)) := by sorry
