-- Prove2me | Theorems.Thm_Coding_exists_padOcc
-- name    : Coding.exists_padOcc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:04:45.809728+00:00
-- url     : https://prove2.me/theorems/76a55c1f-e993-4d06-baa0-c536e5ea6f91
-- title:
--   Coding: exists pad Occ
-- statement:
--   A string of 3·m̄ bits with 0 at the places without a literal is a padded setting.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L95-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L95-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLinks
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Occ
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}

theorem Coding.exists_padOcc (hg : 0 < g) (a : Fin g) {y : List Bool} (hy : y.length = mu g Φ * 3)
    (h0 : ((locals g 3 Φ).all fun r => (litAt 3 Φ (a.val * (mu g Φ * 3) + r)).isSome || !(y.getD r false)) = true) :
    ∃ z : List Bool, z.length = (occOf g Φ a.val).length ∧ padOcc g Φ a z = y := by sorry
