-- Prove2me | Theorems.Thm_ExplicitCost_dropTake_polyT
-- name    : ExplicitCost.dropTake_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:58:36.867547+00:00
-- url     : https://prove2.me/theorems/1bfd820d-5f92-469e-a67b-28261ef5ff19
-- title:
--   Explicit Cost: drop Take poly T
-- statement:
--   Drop and take, for a number of terms given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L113-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L113-L116

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridProcedures
import Definitions.Def_ClauseBound_Alg_CertGridG
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyLists
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG
variable {α : Type} [Enc α]

theorem ExplicitCost.dropTake_polyT {n : α → ℕ → ℕ} {k a b : α → ℕ} {w : α → List Bool} (hn : PolyT fun p : α × ℕ => n p.1 p.2) (hk : Unary k) (ha : PolyT a) (hb : PolyT b) (hw : PolyT w) :
    PolyT fun x => ((w x).drop (((List.range (k x)).map (n x)).sum + a x)).take (b x) := by sorry
