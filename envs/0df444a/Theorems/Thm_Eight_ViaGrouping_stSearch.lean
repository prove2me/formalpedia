-- Prove2me | Theorems.Thm_Eight_ViaGrouping_stSearch
-- name    : Eight.ViaGrouping.stSearch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:06:01.616161+00:00
-- url     : https://prove2.me/theorems/a967df02-4681-4c36-8294-2c759bb8a1d9
-- title:
--   Via Grouping: st Search
-- statement:
--   **«Go through all K^g groupings and fix the first good one.»** For g = 3K⁸ there is a first
--   number x < K^g to which the test says yes, and the grouping number x is good as printed.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L101-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L101-L108

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

theorem Eight.ViaGrouping.stSearch : StSearch := by sorry
