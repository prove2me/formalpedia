-- Prove2me | Theorems.Thm_ExplicitCost_labelLength_polyT
-- name    : ExplicitCost.labelLength_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:40:39.946439+00:00
-- url     : https://prove2.me/theorems/08dd28d1-8b85-40dc-9413-1e278e7fe098
-- title:
--   Explicit Cost: label Length poly T
-- statement:
--   L is computed in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingPoly.lean#L84-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingPoly.lean#L84-L85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_Poly
import Definitions.Def_Exits_Poly
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_PaddedDescent_F_CertNet
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingPoly
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed PaddedDescent.F.CertNet
variable {α : Type} [Enc α]

theorem ExplicitCost.labelLength_polyT {c : α → GroupingInput} (hc : PolyT c) : PolyT fun t => labelLength (c t) := by sorry
