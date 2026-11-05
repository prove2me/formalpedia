-- Prove2me | Theorems.Thm_Eight_ViaGrouping_lamP_eq
-- name    : Eight.ViaGrouping.lamP_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:23:49.230237+00:00
-- url     : https://prove2.me/theorems/48949368-4c7e-475d-8629-c1a70b2a135c
-- title:
--   Via Grouping: lam P eq
-- statement:
--   The number that the program passes to the algorithm for cliques is L = max{1, ⌊(U + gP/K)/K²⌋},
--   written max{1, ⌊(KU + gP)/K³⌋}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L114-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L114-L116

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

theorem Eight.ViaGrouping.lamP_eq (h : IsNetworkP Np c N P B τ S) (x : ℕ) : lamP K g Np (c, x) = Paper.groupedLength K g N.U P := by sorry
