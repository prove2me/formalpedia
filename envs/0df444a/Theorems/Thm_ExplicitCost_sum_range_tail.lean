-- Prove2me | Theorems.Thm_ExplicitCost_sum_range_tail
-- name    : ExplicitCost.sum_range_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:58:53.569087+00:00
-- url     : https://prove2.me/theorems/bc22537c-6934-4aa6-8880-040c0a0cb23b
-- title:
--   Explicit Cost: sum range tail
-- statement:
--   The sum of the first κ of numbers that are constant from the place m on.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L105-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L105-L110

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

theorem ExplicitCost.sum_range_tail (n : ℕ → ℕ) (m κ : ℕ) (h : ∀ k, m ≤ k → n k = n m) : ∑ i ∈ Finset.range κ, n i = ((List.range (min κ m)).map n).sum + (κ - m) * n m := by sorry
