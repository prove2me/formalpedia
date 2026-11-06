-- Prove2me | Theorems.Thm_ExplicitCost_groupingCall_poly
-- name    : ExplicitCost.groupingCall_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:04.112777+00:00
-- url     : https://prove2.me/theorems/b4b9a9f0-e737-47b9-b60c-24510269c404
-- title:
--   Explicit Cost: grouping Call poly
-- statement:
--   The procedure up to the call has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingPoly.lean#L159-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingPoly.lean#L159-L165

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

theorem ExplicitCost.groupingCall_poly : groupingCall.PolyTimeSteps := by sorry
