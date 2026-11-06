-- Prove2me | Theorems.Thm_ExplicitCost_pieceAt_polyT
-- name    : ExplicitCost.pieceAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:06:39.012949+00:00
-- url     : https://prove2.me/theorems/5e10f3b6-81b4-4ba2-a5d3-619110a1f7b9
-- title:
--   Explicit Cost: piece At poly T
-- statement:
--   ι(q).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L94-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L94-L95

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

theorem ExplicitCost.pieceAt_polyT {p : α → Parent} {r κ : α → ℕ} (hp : PolyT p) (hr : PolyT r) (hκ : PolyT κ) : PolyT fun x => pieceAt (p x) (r x) (κ x) := by sorry
