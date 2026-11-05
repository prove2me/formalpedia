-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_length_lAt
-- name    : Eight.ViaGrouping.Table.length_lAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:30.159161+00:00
-- url     : https://prove2.me/theorems/90620968-0dd3-4736-8954-bd5c34fa993e
-- title:
--   Table: length l At
-- statement:
--   The block of the pair p in a string with at least Y_{G,G'} bits has c_p bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L120-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L120-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_length_lAt
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]

theorem Eight.ViaGrouping.Table.length_lAt (Nq : PNet C) {x G G' : ℕ} {θ : List Bool} {p : ℕ × ℕ} (hp : p ∈ prs K g x G G') (hθ : lbLen K g Nq c x G G' ≤ θ.length) :
    (lAt K g Nq c x G G' θ p).length = Nq.cap c p.1 p.2 := by sorry
