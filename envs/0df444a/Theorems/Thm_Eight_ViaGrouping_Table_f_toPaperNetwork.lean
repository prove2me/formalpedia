-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_f_toPaperNetwork
-- name    : Eight.ViaGrouping.Table.f_toPaperNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:12.622208+00:00
-- url     : https://prove2.me/theorems/6cfb6ed7-40e7-4662-9ef1-75d820f5f1bc
-- title:
--   Table: f to Paper Network
-- statement:
--   The factor f_{a,b}(z, θ) of `N.toPaperNetwork`, for a ≠ b and θ of c_{a,b} bits: [z ∈
--   S_a]·f_{a,b}(z, θ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L187-L189
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L187-L189

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

theorem Eight.ViaGrouping.Table.f_toPaperNetwork {a b : Fin g} (hab : a ≠ b) {z θ : List Bool} (hθ : θ.length = N.c a b) :
    N.toPaperNetwork.f a b z θ = if z ∈ N.S a then N.f a b z θ else 0 := by sorry
