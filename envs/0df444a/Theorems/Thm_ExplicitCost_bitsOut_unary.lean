-- Prove2me | Theorems.Thm_ExplicitCost_bitsOut_unary
-- name    : ExplicitCost.bitsOut_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:22:20.482183+00:00
-- url     : https://prove2.me/theorems/12bcbbcf-ae73-446f-9b8c-c2c4620923c4
-- title:
--   Explicit Cost: bits Out unary
-- statement:
--   B' can be written in unary in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingPoly.lean#L98-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingPoly.lean#L98-L109

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

theorem ExplicitCost.bitsOut_unary {c : α → GroupingInput} (hc : PolyT c) : Unary fun t => bitsOut (inK (c t)) (inG (c t)) (inP (c t)) (inB (c t)) := by sorry
