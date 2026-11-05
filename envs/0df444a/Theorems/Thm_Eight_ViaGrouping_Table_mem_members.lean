-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_mem_members
-- name    : Eight.ViaGrouping.Table.mem_members
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:33:05.963166+00:00
-- url     : https://prove2.me/theorems/bd815785-c793-43cf-8c7d-40e791269403
-- title:
--   Table: mem members
-- statement:
--   The nodes of the group G of the grouping number x: the a < g whose digit in x is G.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L80-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L80-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_Prog_NetE_mem_members

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.Table.mem_members {x G a : ℕ} : a ∈ members K g x G ↔ a < g ∧ col K x a = G := by sorry
