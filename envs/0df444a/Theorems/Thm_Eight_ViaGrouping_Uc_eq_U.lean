-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Uc_eq_U
-- name    : Eight.ViaGrouping.Uc_eq_U
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:02:17.655647+00:00
-- url     : https://prove2.me/theorems/98a50a11-36ce-4e21-a4a2-c04272b60921
-- title:
--   Via Grouping: Uc eq U
-- statement:
--   The sum of the given numbers c_{a,b} that the program forms is the total U.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L50-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L50-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.Uc_eq_U (h : IsNetworkP Np c N P B τ S) : Uc g Np.toPaperNetwork c = N.U := by sorry
