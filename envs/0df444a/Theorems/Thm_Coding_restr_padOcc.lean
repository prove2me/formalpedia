-- Prove2me | Theorems.Thm_Coding_restr_padOcc
-- name    : Coding.restr_padOcc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:05:04.471355+00:00
-- url     : https://prove2.me/theorems/ce8079ee-dfa4-4e7a-a648-fc67c57ca024
-- title:
--   Coding: restr pad Occ
-- statement:
--   z_a|_b is the same string in both networks: «let z_a|_b ∈ {0,1}^{c_{a,b}} list the bits of z_a
--   at their occurrences in cluster a» (Section 6).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L196-L211
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L196-L211

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

theorem Coding.restr_padOcc (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : Fin g} (hab : a ≠ b) (z : List Bool) : restr g 3 Φ a.val b.val (padOcc g Φ a z) = restrict g Φ a.val b.val z := by sorry
