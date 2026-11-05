-- Prove2me | Theorems.Thm_ExplicitCost_lenG_tail
-- name    : ExplicitCost.lenG_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:58:23.75951+00:00
-- url     : https://prove2.me/theorems/c4df2c75-ea43-4c07-bc70-d3a6653951cc
-- title:
--   Explicit Cost: len G tail
-- statement:
--   From the place (number of binary digits of y) on, all chunks have the same length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L94-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L94-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridProcedures
import Definitions.Def_ClauseBound_Alg_CertGridG
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyLists
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG
variable {α : Type} [Enc α]

theorem ExplicitCost.lenG_tail (P : PiecesF) (d : ℕ) (tr : Bool) (h lam y q k : ℕ) (hk : (Nat.bits y).length ≤ k) : lenG P d tr h lam y q k = lenG P d tr h lam y q (Nat.bits y).length := by sorry
