-- Prove2me | Theorems.Thm_ExplicitCost_netCap_unary
-- name    : ExplicitCost.netCap_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:04:30.360514+00:00
-- url     : https://prove2.me/theorems/b2c72b46-3268-48a4-8cbc-e591879e7241
-- title:
--   Explicit Cost: net Cap unary
-- statement:
--   c_{a,a'} is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L155-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L155-L155

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

theorem ExplicitCost.netCap_unary {a b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : Unary fun x => netCap (p x) (a x) (b x) := by sorry
