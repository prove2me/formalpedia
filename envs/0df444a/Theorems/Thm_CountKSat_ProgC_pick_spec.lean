-- Prove2me | Theorems.Thm_CountKSat_ProgC_pick_spec
-- name    : CountKSat.ProgC.pick_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:52:31.325344+00:00
-- url     : https://prove2.me/theorems/3ed6e4c7-adf0-4078-ab10-2de707dad15d
-- title:
--   Prog C: pick spec
-- statement:
--   A heart that the search finds has at most k literals, on variables below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L74-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/ProgC.lean#L74-L86

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

theorem CountKSat.ProgC.pick_spec (hθ : ∀ i, 1 ≤ θ i) (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n : ℕ} {ψ : PFml}
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) {s : PFml} {p t : ℕ} (hG : ProgMain.G Node ψ s p t) {H : PCl} {P : PFml}
    (hp : pickK θ k s = some (H, P)) :
    H.length ≤ k ∧ ∀ l ∈ H, l.1 < n := by sorry
