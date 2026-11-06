-- Prove2me | Theorems.Thm_ExplicitCost_pTr_polyT
-- name    : ExplicitCost.pTr_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:03:49.400183+00:00
-- url     : https://prove2.me/theorems/87ae24c3-0628-45bb-a8fe-bffb825ae677
-- title:
--   Explicit Cost: p Tr poly T
-- statement:
--   The direction is read off.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L54-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L54-L54

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

theorem ExplicitCost.pTr_polyT : PolyT fun x => pTr (p x) := by sorry
