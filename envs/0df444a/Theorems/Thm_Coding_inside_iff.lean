-- Prove2me | Theorems.Thm_Coding_inside_iff
-- name    : Coding.inside_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:05:05.823622+00:00
-- url     : https://prove2.me/theorems/54ce1af9-d9ff-417f-8047-e6597de12da6
-- title:
--   Coding: inside iff
-- statement:
--   «z_a[o] = z_a[o'] for every test {o,o'} with both occurrences in cluster a»: Lean's condition at
--   a padded setting is the printed one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L178-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L178-L190

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

theorem Coding.inside_iff (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) (z : List Bool) :
    ((links g 3 Φ a.val a.val).all fun p => (padOcc g Φ a z).getD p.1 false == (padOcc g Φ a z).getD p.2 false) = true ↔
      ((testsBetween g Φ a.val a.val).all fun p => bitAt g Φ a.val z p.1 == bitAt g Φ a.val z p.2) = true := by sorry
