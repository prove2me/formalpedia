-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_length_labOf
-- name    : Eight.ViaGrouping.Table.length_labOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:19.103181+00:00
-- url     : https://prove2.me/theorems/1e37e70a-9ed2-47c2-af29-4d89a084e7ad
-- title:
--   Table: length lab Of
-- statement:
--   «let θ_{a,b} ∈ {0,1}^{c_{a,b}} consist of the bits of Θ(χ(b)) in the block of {a, b}»: it has
--   c_{a,b} bits, if Y_{γ,γ'} ≤ β for all γ ≠ γ' and every Θ(γ') has β bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L134-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L134-L151

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_length_labOf
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}

theorem Eight.ViaGrouping.Table.length_labOf (h : IsNetworkP Np c N P B τ S) (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β)
    (hθ : ∀ G', G' ≠ G → (θ G').length = β) {a b : ℕ} (ha : a ∈ members K g x G) (hb : b < g) (hc : col K x b ≠ G) :
    (labOf K g Np.toPaperNetwork ((c, x), (G.val, List.ofFn θ)) a b).length = Np.cap c a b := by sorry
