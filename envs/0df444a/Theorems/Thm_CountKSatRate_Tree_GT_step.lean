-- Prove2me | Theorems.Thm_CountKSatRate_Tree_GT_step
-- name    : CountKSatRate.Tree.GT_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:35:59.292562+00:00
-- url     : https://prove2.me/theorems/d3044b21-0ce2-4206-aec6-1f2d10cc7234
-- title:
--   Tree: GT step
-- statement:
--   Both children of a node satisfy the invariant after one more step; at the heavy child the second
--   counter grows by q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Tree.lean#L59-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Tree.lean#L59-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSatRate_Tree
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CountKSatRate
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat WidthK.Prog
open WidthK (theta bsum leafC Iface Refines)
open CountKSatRate.Tree
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem CountKSatRate.Tree.GT_step (hθ : ∀ i, 1 ≤ θ i) (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n : ℕ} (ψ : PFml)
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (x : CNode) (p t : ℕ) (l h : CNode) (hG : GT Node ψ n k q x p t)
    (hst : stepC θ k x = some (l, h)) : GT Node ψ n k q l (p + 1) t ∧ GT Node ψ n k q h (p + 1) (t + q) := by sorry
