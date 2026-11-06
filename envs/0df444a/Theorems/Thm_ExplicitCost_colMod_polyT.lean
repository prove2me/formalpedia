-- Prove2me | Theorems.Thm_ExplicitCost_colMod_polyT
-- name    : ExplicitCost.colMod_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:06:56.833589+00:00
-- url     : https://prove2.me/theorems/c02a07ed-512d-4996-9466-dbfbbe6122e4
-- title:
--   Explicit Cost: col Mod poly T
-- statement:
--   The second column, j % g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L101-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L101-L101

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

theorem ExplicitCost.colMod_polyT {β : Type} [Enc β] : PolyT fun v : (Parent × β) × ℕ => v.2 % pG v.1.1 := by sorry
