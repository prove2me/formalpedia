-- Prove2me | Theorems.Thm_ExplicitCost_parentOf_polyT
-- name    : ExplicitCost.parentOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:03:40.789452+00:00
-- url     : https://prove2.me/theorems/50a74b5c-8eae-4901-abcb-9b06a0e31c22
-- title:
--   Explicit Cost: parent Of poly T
-- statement:
--   The parent of a context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L63-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L63-L63

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

theorem ExplicitCost.parentOf_polyT {c : α → Ctx} (hc : PolyT c) : PolyT fun x => parentOf (c x) := by sorry
