-- Prove2me | Theorems.Thm_ExplicitCost_toTable_polyT
-- name    : ExplicitCost.toTable_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:04:39.719953+00:00
-- url     : https://prove2.me/theorems/aac262c6-79e9-4ed6-a3eb-a19b7503458e
-- title:
--   Explicit Cost: to Table poly T
-- statement:
--   A setting as one string.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L77-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L77-L77

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

theorem ExplicitCost.toTable_polyT {q : α → IQ} (hq : PolyT q) : PolyT fun x => toTable (q x) := by sorry
