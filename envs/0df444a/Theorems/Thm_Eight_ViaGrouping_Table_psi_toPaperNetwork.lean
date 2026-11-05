-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_psi_toPaperNetwork
-- name    : Eight.ViaGrouping.Table.psi_toPaperNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:14.793014+00:00
-- url     : https://prove2.me/theorems/7aa68c8b-1d22-4188-9eba-31ed6929b12d
-- title:
--   Table: psi to Paper Network
-- statement:
--   The Ψ_{a,b} defined from the factors of `N.toPaperNetwork` is [z ∈ S_a][z' ∈ S_b]·Ψ_{a,b}(z,
--   z').
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L193-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L193-L199

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}

theorem Eight.ViaGrouping.Table.psi_toPaperNetwork (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) (z z' : List Bool) :
    N.toPaperNetwork.Ψ a b z z' = if z ∈ N.S a then (if z' ∈ N.S b then N.Ψ a b z z' else 0) else 0 := by sorry
