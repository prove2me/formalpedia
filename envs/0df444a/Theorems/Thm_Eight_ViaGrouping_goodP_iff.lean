-- Prove2me | Theorems.Thm_Eight_ViaGrouping_goodP_iff
-- name    : Eight.ViaGrouping.goodP_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:03:07.832196+00:00
-- url     : https://prove2.me/theorems/cd2a5b91-1b7c-4b04-96cd-9a887b77179f
-- title:
--   Via Grouping: good P iff
-- statement:
--   «Being good depends only on the numbers c_{a,b}»: the test of the program says yes to x exactly
--   if the grouping number x is good as printed, with (G1) as printed and with the given P in (G2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L60-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L60-L79

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

theorem Eight.ViaGrouping.goodP_iff (hK0 : 0 < K) (h : IsNetworkP Np c N P B τ S) (x : ℕ) : goodP K g Np (c, x) = true ↔ Good N.c P (Paper.grouping hK0 x) := by sorry
