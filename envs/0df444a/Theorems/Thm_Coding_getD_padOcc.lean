-- Prove2me | Theorems.Thm_Coding_getD_padOcc
-- name    : Coding.getD_padOcc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:23:21.097196+00:00
-- url     : https://prove2.me/theorems/f8c0f1d8-60a0-48e9-a1e2-7ce2fa028e83
-- title:
--   Coding: get D pad Occ
-- statement:
--   The bit of the padded string at place i of the cluster.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L45-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L45-L48

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

theorem Coding.getD_padOcc (a : Fin g) (z : List Bool) {i : ℕ} (hi : i < mu g Φ * 3) :
    (padOcc g Φ a z).getD i false = (decide (i % 3 < (Φ.getD (a.val * mu g Φ + i / 3) []).length) && bitAt g Φ a.val z (a.val * mu g Φ + i / 3, i % 3)) := by sorry
