-- Prove2me | Theorems.Thm_Coding_zero_padOcc
-- name    : Coding.zero_padOcc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:03:23.163483+00:00
-- url     : https://prove2.me/theorems/e7112abf-f441-4575-ac9b-7c866723b59e
-- title:
--   Coding: zero pad Occ
-- statement:
--   A padded setting has 0 at the places without a literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L85-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L85-L92

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}

theorem Coding.zero_padOcc (hg : 0 < g) (a : Fin g) (z : List Bool) :
    ((locals g 3 Φ).all fun r => (litAt 3 Φ (a.val * (mu g Φ * 3) + r)).isSome || !((padOcc g Φ a z).getD r false)) = true := by sorry
