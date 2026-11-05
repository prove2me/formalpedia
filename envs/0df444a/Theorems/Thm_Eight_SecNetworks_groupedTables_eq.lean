-- Prove2me | Theorems.Thm_Eight_SecNetworks_groupedTables_eq
-- name    : Eight.SecNetworks.groupedTables_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:39:15.671698+00:00
-- url     : https://prove2.me/theorems/1a12082d-dab3-41ce-9f5c-1e00d06a7926
-- title:
--   Sec Networks: grouped Tables eq
-- statement:
--   **Proof of Lemma 1, «The algorithm»: the display of W̃_γ.** For Θ : [K] ∖ {γ} → {0,1}^L,
--   W̃_γ(Θ) = [all appended bits are 0] Σ_{(z_a), a ∈ G_γ} ∏_{a ∈ G_γ} W_a(z_a) ∏_{{a,b} ⊆ G_γ}
--   Ψ_{a,b}(z_a, z_b) ∏_{a ∈ G_γ, b ∉ G_γ} f_{a,b}(z_a, θ_{a,b}), each z_a ranging over S_a. Same as in
--   the paper. In Lean's terms: Θ is a function on all
--   of [K], whose value at γ is not read; (z_a) is a function on all nodes, with the empty string
--   outside G_γ; the pairs {a, b} ⊆ G_γ are the pairs a < b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Tables.lean#L66-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Tables.lean#L66-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_Tables
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Paper
variable {C : Type} {g K : ℕ}

theorem Eight.SecNetworks.groupedTables_eq (Np : NetworkProcedures C) (c : C) (N : Paper.Network (Fin g) (List Bool) (List Bool)) (hK0 : 0 < K) (x L : ℕ) (γ : Fin K) (Θ : Fin K → List Bool)
    (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    groupedTables Np c N hK0 x L γ Θ =
      (if ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np c x γ γ' (Θ γ'), bit = false then 1 else 0) *
        ∑ z ∈ tuples (fun a => grouping hK0 x a = γ) N.S [],
          (∏ a with grouping hK0 x a = γ, N.W a (z a)) *
            (∏ p ∈ pairs (Fin g) with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
            ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np c hK0 x Θ p.1 p.2) := by sorry
