-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_isPaperNetwork
-- name    : Eight.ViaGrouping.Table.isPaperNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:49:17.048334+00:00
-- url     : https://prove2.me/theorems/6ea8cdd9-fff2-4489-ba41-066777ae395a
-- title:
--   Table: is Paper Network
-- statement:
--   The network `N.toPaperNetwork` with the procedures `Np.toPaperNetwork` is a network in the sense
--   of `Paper.IsNetwork` with the same P and B. (These procedures do not depend on what is given for B.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L65-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L65-L68

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

theorem Eight.ViaGrouping.Table.isPaperNetwork (h : IsNetworkP Np c N P B τ S) :
    Paper.IsNetwork Np.toPaperNetwork c N.toPaperNetwork P B (2 * τ + 1) (S + (size c + 2 * size g + 4 * P + 6)) := by sorry
