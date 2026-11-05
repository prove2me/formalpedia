-- Prove2me | Theorems.Thm_Coding_mu_pos_of_occ
-- name    : Coding.mu_pos_of_occ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:29:42.89547+00:00
-- url     : https://prove2.me/theorems/792e16de-a927-43dc-922e-8174fe4b2d30
-- title:
--   Coding: mu pos of occ
-- statement:
--   If Φ has an occurrence, then m̄ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L34-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLinks.lean#L34-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_OccLinks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}

theorem Coding.mu_pos_of_occ (hg : 0 < g) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) : 0 < mu g Φ := by sorry
