-- Prove2me | Theorems.Thm_ExplicitCost_totalL_unary
-- name    : ExplicitCost.totalL_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:56:20.665385+00:00
-- url     : https://prove2.me/theorems/08ecca0d-b7a4-4724-8b31-e8475d9ca276
-- title:
--   Explicit Cost: total L unary
-- statement:
--   The total of the network of a pattern is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L73-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L73-L76

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

theorem ExplicitCost.totalL_unary {p d lam y : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hl : Unary lam) (hy : PolyT y) :
    Unary fun x => totalG (listsAsPieces (L x)) (p x) (d x) (tr x) 0 (lam x) (y x) := by sorry
