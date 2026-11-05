-- Prove2me | Theorems.Thm_Eight_ViaGrouping_grouping_number
-- name    : Eight.ViaGrouping.grouping_number
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:04:03.026505+00:00
-- url     : https://prove2.me/theorems/835ea17b-7c11-4662-8eb1-6e1bc75b5173
-- title:
--   Via Grouping: grouping number
-- statement:
--   Every grouping has a number below K^g: its values are the digits in base K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L84-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L84-L89

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

theorem Eight.ViaGrouping.grouping_number (hK0 : 0 < K) (χ : Fin g → Fin K) : ∃ x < K ^ g, Paper.grouping hK0 x = χ := by sorry
