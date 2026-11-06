-- Prove2me | Theorems.Thm_ExplicitCost_capL_unary
-- name    : ExplicitCost.capL_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:00:46.854013+00:00
-- url     : https://prove2.me/theorems/61013f46-925b-4e76-8e4d-e02e19fb35b8
-- title:
--   Explicit Cost: cap L unary
-- statement:
--   c^row_i or c^col_i, cut at 2λ, is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L42-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L42-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridProcedures
import Definitions.Def_ClauseBound_Alg_CertGridG
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyLists
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG
variable {α : Type} [Enc α]
variable {L : α → Lists} (hL : PolyT L)
include hL

theorem ExplicitCost.capL_unary {tr : α → Bool} {lam i : α → ℕ} (ht : PolyT tr) (hl : Unary lam) (hi : PolyT i) : Unary fun x => (listsAsPieces (L x)).cap (tr x) 0 (lam x) (i x) := by sorry
