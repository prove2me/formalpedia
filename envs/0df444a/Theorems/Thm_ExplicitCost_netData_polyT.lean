-- Prove2me | Theorems.Thm_ExplicitCost_netData_polyT
-- name    : ExplicitCost.netData_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:37.668778+00:00
-- url     : https://prove2.me/theorems/e1fafbdf-e7e2-42a9-8747-f219c9e87665
-- title:
--   Explicit Cost: net Data poly T
-- statement:
--   K, g and what an algorithm for networks is given, for the network of a parent.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L172-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L172-L174

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyLists
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyQueries
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
variable {α : Type} [Enc α]

theorem ExplicitCost.netData_polyT (c : ℕ) {p : α → Parent} (hp : PolyT p) : PolyT fun x => netData c (p x) := by sorry
