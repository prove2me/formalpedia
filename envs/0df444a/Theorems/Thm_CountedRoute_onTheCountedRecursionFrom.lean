-- Prove2me | Theorems.Thm_CountedRoute_onTheCountedRecursionFrom
-- name    : CountedRoute.onTheCountedRecursionFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:00:51.343072+00:00
-- url     : https://prove2.me/theorems/692941a1-8d86-4f95-9eac-55e539dd807b
-- title:
--   Counted Route: on The Counted Recursion From
-- statement:
--   The chain on the machine of Theorem A (b).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/CountedRoute/Main.lean#L63-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/CountedRoute/Main.lean#L63-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRoute_Defs
import Definitions.Def_ThmVariables_PartA
import Definitions.Def_NamesInOrder_Main
import Definitions.Def_MainRoute_GeneralMain
import Definitions.Def_CountedToPadded_Main
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedInstance_Main
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_CountedRoute_Main
set_option autoImplicit false
section
section
open CountedRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms PairsToBound MainRoute NamesInOrder
open Sat3 (CNF)

theorem CountedRoute.onTheCountedRecursionFrom : OnTheCountedRecursionFrom := by sorry
