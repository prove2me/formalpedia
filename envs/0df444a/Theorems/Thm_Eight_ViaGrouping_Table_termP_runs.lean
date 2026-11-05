-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_termP_runs
-- name    : Eight.ViaGrouping.Table.termP_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:20:00.024408+00:00
-- url     : https://prove2.me/theorems/f2e03ab9-c5e2-4386-b675-13812f365342
-- title:
--   Table: term P runs
-- statement:
--   One of the g² factors of a term of W̃_γ(Θ). The index i < g·g stands for the pair of nodes (a,
--   b) = (i / g, i % g). The factor is 1, or [z_a ∈ S_a]·W_a(z_a), or [z_a ∈ S_a][z_b ∈
--   S_b]·Ψ_{a,b}(z_a, z_b), or [z_a ∈ S_a]·f_{a,b}(z_a, θ_{a,b}).
--   It costs at most 4τ + 3 steps (two tests and one call, in the case of Ψ) and is at most 2^B in
--   absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L218-L304
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L218-L304

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}

theorem Eight.ViaGrouping.Table.termP_runs (h : IsNetworkP Np c N P B τ S) (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β)
    (hθ : ∀ G', G' ≠ G → (θ G').length = β) (y : ℕ) {i : ℕ} (hi : i < g * g) :
    (termP K g Np).Runs ((((c, x), (G.val, List.ofFn θ)), y), i) (4 * τ + 3) (2 * size ((((c, x), (G.val, List.ofFn θ)), y), i) + S + 12)
      (termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)) ∧
    (termVal K g Np.toPaperNetwork N.toPaperNetwork ((((c, x), (G.val, List.ofFn θ)), y), i)).natAbs ≤ 2 ^ B := by sorry
