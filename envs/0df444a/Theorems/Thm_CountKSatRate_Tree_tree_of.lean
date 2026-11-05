-- Prove2me | Theorems.Thm_CountKSatRate_Tree_tree_of
-- name    : CountKSatRate.Tree.tree_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:45:32.237078+00:00
-- url     : https://prove2.me/theorems/fed9ea60-b6fe-4d48-89e2-b9f3fb90d0a9
-- title:
--   Tree: tree of
-- statement:
--   The sparsification lemma for counting with the side list bounded by B, for any thresholds and
--   bounds that satisfy `Iface` and `Refines`. Every leaf satisfies the invariant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Tree.lean#L91-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Tree.lean#L91-L144

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
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open CountKSatRate
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat WidthK.Prog
open WidthK (theta bsum leafC Iface Refines)
open CountKSatRate.Tree
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem CountKSatRate.Tree.tree_of (hSC : StStepCount) (hRC : StRootCount) (hSL : StSumLeaves) (hθ : ∀ i, 1 ≤ θ i) {n : ℕ} (hI : Iface θ k D T q leafB Ok Node)
    (hR : Refines θ k) {hv B : ℕ} (hT : T < (hv + 1) * q) (hB : n * q + k * T ≤ B * q) (ψ : PFml) (hOk : Ok (toFin ψ))
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    (leaves (stepC θ k) D (rootP ψ, taut n)).length ≤ ∑ j ∈ range (hv + 1), D.choose j ∧
    (∀ x ∈ leaves (stepC θ k) D (rootP ψ, taut n), stepC θ k x = none ∧ (leafF x).length ≤ leafB + B ∧
      (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∃ p t, GT Node ψ n k q x p t) ∧
    cntN n ψ = ((leaves (stepC θ k) D (rootP ψ, taut n)).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1, x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ B ∧
        (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n := by sorry
