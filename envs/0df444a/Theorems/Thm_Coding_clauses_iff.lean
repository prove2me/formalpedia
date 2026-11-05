-- Prove2me | Theorems.Thm_Coding_clauses_iff
-- name    : Coding.clauses_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:05:28.610575+00:00
-- url     : https://prove2.me/theorems/f6ceaa25-d584-4fcd-aa85-5bdd59129699
-- title:
--   Coding: clauses iff
-- statement:
--   «every clause of cluster a has a true occurrence»: Lean's condition at a padded setting is the
--   printed one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L161-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L161-L174

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
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_snd
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.snd


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}

theorem Coding.clauses_iff (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) (z : List Bool) :
    ((rows g Φ).all fun c => !(decide (a.val * mu g Φ + c < Φ.length)) ||
        (List.range 3).any fun j => (litAt 3 Φ ((a.val * mu g Φ + c) * 3 + j)).map Prod.snd == some ((padOcc g Φ a z).getD (c * 3 + j) false)) = true ↔
      ((List.range' (a.val * mu g Φ) (mu g Φ)).all fun e => !(decide (e < Φ.length)) || (List.range (Φ.getD e []).length).any fun j => isTrue g Φ a.val z (e, j)) = true := by sorry
