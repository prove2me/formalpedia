-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_natAbs_le
-- name    : Eight.ViaGrouping.Table.natAbs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:11:29.751266+00:00
-- url     : https://prove2.me/theorems/23e3965d-a2ed-4a58-8b18-c5a0143ec44e
-- title:
--   Table: nat Abs le
-- statement:
--   |z| ≤ 2^n, said of the natural number `z.natAbs`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L94-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L94-L96

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

theorem Eight.ViaGrouping.Table.natAbs_le {z : ℤ} {n : ℕ} (h : |z| ≤ 2 ^ n) : z.natAbs ≤ 2 ^ n := by sorry
