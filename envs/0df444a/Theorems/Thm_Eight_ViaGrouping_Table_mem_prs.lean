-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_mem_prs
-- name    : Eight.ViaGrouping.Table.mem_prs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:17.42019+00:00
-- url     : https://prove2.me/theorems/552cd8e3-8603-4623-96dd-8036ee8d7bca
-- title:
--   Table: mem prs
-- statement:
--   A pair of a node of G and a node of G' is in the list of the pairs that have a block.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L127-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L127-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_Prog_NetE_mem_prs

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.Table.mem_prs {x G G' a b : ℕ} (ha : a ∈ members K g x G) (hb : b ∈ members K g x G') : (a, b) ∈ prs K g x G G' := by sorry
