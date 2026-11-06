-- Prove2me | Theorems.Thm_ExplicitCost_recursionPluggedFrom
-- name    : ExplicitCost.recursionPluggedFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:23:00.047015+00:00
-- url     : https://prove2.me/theorems/0b3e8d71-971e-404d-975b-f678b1625d69
-- title:
--   Explicit Cost: recursion Plugged From
-- statement:
--   **Theorem A (b) with the pieces computed by their algorithm**, from the form with the priced
--   oracle.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndPlugged.lean#L28-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/EndPlugged.lean#L28-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_EndBounds
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndPlugged
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.recursionPluggedFrom : RecursionPluggedFrom := by sorry
