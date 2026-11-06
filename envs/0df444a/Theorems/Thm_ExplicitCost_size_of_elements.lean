-- Prove2me | Theorems.Thm_ExplicitCost_size_of_elements
-- name    : ExplicitCost.size_of_elements
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:51.01553+00:00
-- url     : https://prove2.me/theorems/0fe1c657-7bf9-4891-844b-3d9e970f1e76
-- title:
--   Explicit Cost: size of elements
-- statement:
--   A list of k elements, each of size below s, has size at most ks + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L103-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L103-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverRoom
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.size_of_elements {α : Type} [HasSize α] (l : List α) (s : ℕ) (h : ∀ x ∈ l, size x + 1 ≤ s) : size l ≤ l.length * s + 1 := by sorry
