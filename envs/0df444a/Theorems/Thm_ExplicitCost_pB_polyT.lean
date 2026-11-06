-- Prove2me | Theorems.Thm_ExplicitCost_pB_polyT
-- name    : ExplicitCost.pB_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:03:07.128127+00:00
-- url     : https://prove2.me/theorems/79f87303-77e6-414c-805a-9bb5fd693a36
-- title:
--   Explicit Cost: p B poly T
-- statement:
--   The caller's B is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L50-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L50-L50

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

theorem ExplicitCost.pB_polyT : PolyT fun x => pB (p x) := by sorry
