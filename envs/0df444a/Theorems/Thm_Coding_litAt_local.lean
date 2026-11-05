-- Prove2me | Theorems.Thm_Coding_litAt_local
-- name    : Coding.litAt_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:31:46.35547+00:00
-- url     : https://prove2.me/theorems/cade7ec1-8bb8-4cc3-a042-6c97b5422012
-- title:
--   Coding: lit At local
-- statement:
--   What stands at place r of cluster a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L78-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L78-L82

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

theorem Coding.litAt_local (a r : ℕ) : litAt 3 Φ (a * (mu g Φ * 3) + r) = if r % 3 < (Φ.getD (a * mu g Φ + r / 3) []).length then some (litOf Φ (a * mu g Φ + r / 3, r % 3)) else none := by sorry
