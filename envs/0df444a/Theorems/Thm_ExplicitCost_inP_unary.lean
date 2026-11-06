-- Prove2me | Theorems.Thm_ExplicitCost_inP_unary
-- name    : ExplicitCost.inP_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:40:41.46275+00:00
-- url     : https://prove2.me/theorems/a508a63a-0d4e-4cef-9d01-5053eec19f5a
-- title:
--   Explicit Cost: in P unary
-- statement:
--   P is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingPoly.lean#L48-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingPoly.lean#L48-L48

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

theorem ExplicitCost.inP_unary {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => inP (c t) := by sorry
