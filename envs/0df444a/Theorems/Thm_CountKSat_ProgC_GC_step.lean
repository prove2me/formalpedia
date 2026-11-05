-- Prove2me | Theorems.Thm_CountKSat_ProgC_GC_step
-- name    : CountKSat.ProgC.GC_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:48.329469+00:00
-- url     : https://prove2.me/theorems/5a43c094-a66b-4df5-b7c4-0076581018af
-- title:
--   Prog C: GC step
-- statement:
--   Both children of a node satisfy `GC` with one more step (p + 1); the second child h, which gets
--   the shortened clauses P and, on its side list, the negations of the literals of H, also has its
--   counter t raised by q (t + q).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L98-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L98-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_ProgC
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.ProgC
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem CountKSat.ProgC.GC_step (hθ : ∀ i, 1 ≤ θ i) (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n : ℕ} (ψ : PFml)
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (x : CNode) (p t : ℕ) (l h : CNode) (hG : GC Node ψ n k x p t)
    (hst : stepC θ k x = some (l, h)) : GC Node ψ n k l (p + 1) t ∧ GC Node ψ n k h (p + 1) (t + q) := by sorry
