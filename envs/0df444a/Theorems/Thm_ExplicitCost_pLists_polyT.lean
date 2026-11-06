-- Prove2me | Theorems.Thm_ExplicitCost_pLists_polyT
-- name    : ExplicitCost.pLists_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:01:52.012508+00:00
-- url     : https://prove2.me/theorems/3536a2ac-0edf-4d59-b73d-322cadbafb59
-- title:
--   Explicit Cost: p Lists poly T
-- statement:
--   The lists are read off.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L52-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L52-L52

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
variable {p : α → Parent} (hp : PolyT p)
include hp

theorem ExplicitCost.pLists_polyT : PolyT fun x => pLists (p x) := by sorry
