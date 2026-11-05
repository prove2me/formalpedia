-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_length_zA
-- name    : Eight.ViaGrouping.Table.length_zA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:07:50.4082+00:00
-- url     : https://prove2.me/theorems/b75c27f4-8beb-4792-91f3-932819fa6b6b
-- title:
--   Table: length z A
-- statement:
--   The part z_a of the setting number y of the group G has P_a bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L112-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L112-L116

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_length_zA
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]

theorem Eight.ViaGrouping.Table.length_zA (Nq : PNet C) {x G : ℕ} {θs : List (List Bool)} {y a : ℕ} (ha : a ∈ members K g x G) :
    (zA K g Nq (((c, x), (G, θs)), y) a).length = Nq.n c a := by sorry
