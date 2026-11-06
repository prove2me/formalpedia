-- Prove2me | Theorems.Thm_ExplicitCost_pK_polyT
-- name    : ExplicitCost.pK_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:03:19.533195+00:00
-- url     : https://prove2.me/theorems/c42df0f1-69fc-44ef-b03e-5d4e4fce7235
-- title:
--   Explicit Cost: p K poly T
-- statement:
--   K is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L44-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L44-L44

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

theorem ExplicitCost.pK_polyT : PolyT fun x => pK (p x) := by sorry
