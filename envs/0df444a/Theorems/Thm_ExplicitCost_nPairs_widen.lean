-- Prove2me | Theorems.Thm_ExplicitCost_nPairs_widen
-- name    : ExplicitCost.nPairs_widen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:54:25.141481+00:00
-- url     : https://prove2.me/theorems/ee1d8363-cb71-4855-96d2-389cdd9bb8c6
-- title:
--   Explicit Cost: n Pairs widen
-- statement:
--   The number of factors of a term is the same on the widened input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L144-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L144-L147

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

theorem ExplicitCost.nPairs_widen (v : X0 NetInput × ℕ) : nPairs (gOf (widen₁ K g v).1) (widen₁ K g v) = nPairs g v := by sorry
