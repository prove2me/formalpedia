-- Prove2me | Theorems.Thm_ExplicitCost_isRect_polyT
-- name    : ExplicitCost.isRect_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:01.790768+00:00
-- url     : https://prove2.me/theorems/6f5f86e5-69de-4f0b-87dd-3f8f20182651
-- title:
--   Explicit Cost: is Rect poly T
-- statement:
--   The number j names a rectangle when j / g < j % g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L104-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L104-L104

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

theorem ExplicitCost.isRect_polyT {β : Type} [Enc β] : PolyT fun v : (Parent × β) × ℕ => decide (v.2 / pG v.1.1 < v.2 % pG v.1.1) := by sorry
