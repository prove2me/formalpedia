-- Prove2me | Theorems.Thm_ExplicitCost_toLists_polyT_data
-- name    : ExplicitCost.toLists_polyT_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:05:41.167318+00:00
-- url     : https://prove2.me/theorems/5910ce55-0aaa-4f9a-a882-de36a80cc022
-- title:
--   Explicit Cost: to Lists poly T data
-- statement:
--   Cutting a setting into its K − 1 strings of λ bits, for K given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L177-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L177-L179

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

theorem ExplicitCost.toLists_polyT_data {K lam : α → ℕ} {q : α → TableQuery} (hK : Unary K) (hl : PolyT lam) (hq : PolyT q) : PolyT fun x => toLists (K x) (lam x) (q x) := by sorry
