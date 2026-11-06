-- Prove2me | Theorems.Thm_Coding_padOcc_inj
-- name    : Coding.padOcc_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:28.113617+00:00
-- url     : https://prove2.me/theorems/1d498a82-5af9-49e0-9700-17dc6a0af05f
-- title:
--   Coding: pad Occ inj
-- statement:
--   Padding is one to one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L117-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L117-L127

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

theorem Coding.padOcc_inj (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) {z z' : List Bool} (hz : z.length = (occOf g Φ a.val).length) (hz' : z'.length = (occOf g Φ a.val).length)
    (h : padOcc g Φ a z = padOcc g Φ a z') : z = z' := by sorry
