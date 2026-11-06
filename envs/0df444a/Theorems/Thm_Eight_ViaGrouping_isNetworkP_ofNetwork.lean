-- Prove2me | Theorems.Thm_Eight_ViaGrouping_isNetworkP_ofNetwork
-- name    : Eight.ViaGrouping.isNetworkP_ofNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:30:44.871964+00:00
-- url     : https://prove2.me/theorems/1f0dfcae-fe3e-4dfd-9e71-1462e358c27c
-- title:
--   Via Grouping: is Network P of Network
-- statement:
--   **The bridge.** A network of proof/networks/Paper with parameters P, B, τ, together with a
--   procedure Q that computes its Ψ on settings within τ steps, is a network in the sense of Definition
--   2 (without the part of condition (iii) that gives B to the algorithm as input) with parameters P, B +
--   1, τ.
--   The test for membership forgets the query and says yes in one step, on states of size 2; hence S + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L87-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L87-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}

theorem Eight.ViaGrouping.isNetworkP_ofNetwork {C : Type} [HasSize C] {Np : Paper.NetworkProcedures C} {Pf : C → ℕ} {Q : Stepped (C × PsiQ) ℤ} {c : C}
    {N : Paper.Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ} (hP : 1 ≤ P) (hτ : 1 ≤ τ) (h : Paper.IsNetwork Np c N P B τ S) (hPf : Pf c = P)
    (hQ : ∀ a b : Fin g, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Q.Runs (c, ((a.val, b.val), (z, z'))) τ S (N.Ψ a b z z')) :
    IsNetworkP (ofProcs Np Pf Q) c (ofNetwork N fun a => Np.n c a) P (B + 1) τ (S + 2) := by sorry
