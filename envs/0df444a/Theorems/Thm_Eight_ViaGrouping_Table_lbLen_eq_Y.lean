-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_lbLen_eq_Y
-- name    : Eight.ViaGrouping.Table.lbLen_eq_Y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:11:16.152019+00:00
-- url     : https://prove2.me/theorems/261a9873-1763-40f2-b9c8-3645b36f77d1
-- title:
--   Table: lb Len eq Y
-- statement:
--   Y_{γ,γ'} as the programs compute it (a sum over a list of pairs of numbers) is the Y_{γ,γ'} of
--   the paper.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L431-L434
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L431-L434

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

theorem Eight.ViaGrouping.Table.lbLen_eq_Y (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x : ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    lbLen K g Np.toPaperNetwork c x γ.val γ'.val = Y N.c (Paper.grouping hK0 x) γ γ' := by sorry
