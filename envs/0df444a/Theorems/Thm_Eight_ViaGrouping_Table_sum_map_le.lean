-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_sum_map_le
-- name    : Eight.ViaGrouping.Table.sum_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:34:57.989561+00:00
-- url     : https://prove2.me/theorems/f8498412-208b-492b-a4f1-44e721a750db
-- title:
--   Table: sum map le
-- statement:
--   A sum of numbers that are at most M is at most their number times M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L84-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L84-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Prog_NetE_sum_map_le
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.Table.sum_map_le {ι : Type} (l : List ι) (f : ι → ℕ) (M : ℕ) (h : ∀ i ∈ l, f i ≤ M) : (l.map f).sum ≤ l.length * M := by sorry
