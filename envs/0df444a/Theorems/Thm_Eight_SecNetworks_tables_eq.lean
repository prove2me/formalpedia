-- Prove2me | Theorems.Thm_Eight_SecNetworks_tables_eq
-- name    : Eight.SecNetworks.tables_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:39:24.010893+00:00
-- url     : https://prove2.me/theorems/8e8e8104-40df-45c8-880b-b8a60e1ccb7b
-- title:
--   Sec Networks: tables eq
-- statement:
--   **The display of W̃_γ for a network as Definition 2 prints it** (with sets S_a of settings and
--   functions Ψ_{a,b} of its own): the tables on which the algorithm of Lemma 1 runs are given by the
--   formula of the paper in terms of
--   W_a, Ψ_{a,b}, f_{a,b} and S_a of N, for Θ : [K] ∖ {γ} → {0,1}^L and Y_{γ,γ'} ≤ L. Same as in the
--   paper; the remarks at `groupedTables_eq` apply.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Tables.lean#L154-L193
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Tables.lean#L154-L193

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

theorem Eight.SecNetworks.tables_eq [HasSize C] {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ} (h : IsNetwork Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ)
    (hL : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (grouping hK0 x) γ γ' ≤ L) (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L γ Θ =
      (if ∀ γ', γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np.toPaperNetwork c x γ γ' (Θ γ'), bit = false then 1 else 0) *
        ∑ z ∈ tuples (fun a => grouping hK0 x a = γ) N.S [],
          (∏ a with grouping hK0 x a = γ, N.W a (z a)) *
            (∏ p ∈ pairs (Fin g) with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 = γ, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
            ∏ p : Fin g × Fin g with grouping hK0 x p.1 = γ ∧ grouping hK0 x p.2 ≠ γ, N.f p.1 p.2 (z p.1) (thetaAt Np.toPaperNetwork c hK0 x Θ p.1 p.2) := by sorry
