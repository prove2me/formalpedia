-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Y_le_of_good
-- name    : Eight.ViaGrouping.Y_le_of_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:04:31.286918+00:00
-- url     : https://prove2.me/theorems/0c73e49e-e0cd-4ee5-b105-0c7c3765b108
-- title:
--   Via Grouping: Y le of good
-- statement:
--   «… so that Y_{γ,γ'} ≤ L», for a good grouping.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L119-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Search.lean#L119-L120

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

theorem Eight.ViaGrouping.Y_le_of_good (hK0 : 0 < K) {χ : Fin g → Fin K} (hχ : Good N.c P χ) {γ γ' : Fin K} (hne : γ ≠ γ') : Y N.c χ γ γ' ≤ Paper.groupedLength K g N.U P := by sorry
