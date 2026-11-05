-- Prove2me | Theorems.Thm_CountKSat_ProgC_sparsifiesC_of
-- name    : CountKSat.ProgC.sparsifiesC_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:33.767302+00:00
-- url     : https://prove2.me/theorems/e4ea60ec-1251-481a-b379-2147f28e20fa
-- title:
--   Prog C: sparsifies C of
-- statement:
--   The sparsification lemma for counting, for one n, any thresholds θ and any bounds D, T, q, leafB
--   for which the facts on finite sets (`Iface`) and the
--   refinement (`Refines`) hold. hv bounds the number of steps on a path that go to the second child.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L140-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L140-L196

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
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
open CountKSat.ProgC
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem CountKSat.ProgC.sparsifiesC_of (hSC : StStepCount) (hRC : StRootCount) (hSL : StSumLeaves) (hθ : ∀ i, 1 ≤ θ i) {n : ℕ} (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {hv : ℕ}
    (hT : T < (hv + 1) * q) (ψ : PFml) (hOk : Ok (toFin ψ)) (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    (leaves (stepC θ k) D (rootP ψ, taut n)).length ≤ ∑ j ∈ range (hv + 1), D.choose j ∧
    (∀ x ∈ leaves (stepC θ k) D (rootP ψ, taut n), stepC θ k x = none ∧ (leafF x).length ≤ leafB + (n + k * D) ∧
      (∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ i < n, ∃ C ∈ leafF x, ∃ l ∈ C, l.1 = i) ∧
    cntN n ψ = ((leaves (stepC θ k) D (rootP ψ, taut n)).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1, (leafF x).length ≤ ψ.length * 2 ^ k + (n + k * D) ∧
        ∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n := by sorry
