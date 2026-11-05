-- Prove2me | Theorems.Thm_Coding_getD_padOcc_occ
-- name    : Coding.getD_padOcc_occ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:09:00.230754+00:00
-- url     : https://prove2.me/theorems/c01d60e2-0737-4579-9446-973e65cd0c8e
-- title:
--   Coding: get D pad Occ occ
-- statement:
--   The padded string has the bit z_a[o] at the place of the occurrence o.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L58-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L58-L69

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

theorem Coding.getD_padOcc_occ (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) (z : List Bool) {o : ℕ × ℕ} (ho : o ∈ occOf g Φ a.val) :
    (padOcc g Φ a z).getD (place o - a.val * (mu g Φ * 3)) false = bitAt g Φ a.val z o := by sorry
