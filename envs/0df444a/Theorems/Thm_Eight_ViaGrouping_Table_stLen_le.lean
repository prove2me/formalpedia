-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_stLen_le
-- name    : Eight.ViaGrouping.Table.stLen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:25:57.699806+00:00
-- url     : https://prove2.me/theorems/f5dd6a89-033a-4f61-bdac-7a16b8070489
-- title:
--   Table: st Len le
-- statement:
--   «at most (2^P)^{2g/K} terms»: a setting of a group with at most m nodes has at most P·m bits,
--   since P_a ≤ P.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L100-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L100-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_stLen_le
import Theorems.Thm_PaddedDescent_F_RebalF_stLen_le
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.Table.stLen_le (h : IsNetworkP Np c N P B τ S) {x G m : ℕ} (hm : (members K g x G).length ≤ m) : stLen K g Np.toPaperNetwork c x G ≤ P * m := by sorry
