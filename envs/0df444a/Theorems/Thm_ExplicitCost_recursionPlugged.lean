-- Prove2me | Theorems.Thm_ExplicitCost_recursionPlugged
-- name    : ExplicitCost.recursionPlugged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:35:29.459575+00:00
-- url     : https://prove2.me/theorems/8d8f0ff1-9101-4153-a707-8bb6bb83ed83
-- title:
--   Explicit Cost: recursion Plugged
-- statement:
--   **Theorem A (b), with the pieces computed by their algorithm.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Main.lean#L93-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Main.lean#L93-L93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Base
import Definitions.Def_CountedRecursion_BothNetworks
import Definitions.Def_CountedRecursion_ChildIsGood
import Definitions.Def_CountedRecursion_ProcedureCost
import Definitions.Def_CountedRecursion_SolverStep
import Definitions.Def_CountedRecursion_Meets
import Definitions.Def_CountedRecursion_Expansion
import Definitions.Def_CountedRecursion_Totals
import Definitions.Def_CountedRecursion_CaseTwo
import Definitions.Def_CountedRecursion_LabelCrude
import Definitions.Def_CountedRecursion_TotalCount
import Definitions.Def_CountedRecursion_TotalRoom
import Definitions.Def_CountedRecursion_RoomWithin
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_CountedRecursion_PolyAll
import Definitions.Def_CountedRecursion_EndCounted
import Definitions.Def_CountedRecursion_EndPlugged
import Definitions.Def_CountedRecursion_EndSolves
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_ExplicitCost_GroupingCall
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_Value_End
import Definitions.Def_Tower_TowerRuns
import Definitions.Def_PiecesCounted_Oracle
import Definitions.Def_PiecesCounted_Assume
import Definitions.Def_CountedRecursion_Main
set_option autoImplicit false
section
section
open ExplicitCost
open QueryMachines

theorem ExplicitCost.recursionPlugged : RecursionPlugged := by sorry
