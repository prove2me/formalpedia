-- Prove2me | Theorems.Thm_Coding_place_sub
-- name    : Coding.place_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:33:55.523514+00:00
-- url     : https://prove2.me/theorems/6f88bd65-eca1-49ea-b0d2-162f6d1dc891
-- title:
--   Coding: place sub
-- statement:
--   The place of an occurrence of cluster a within the cluster.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L51-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L51-L55

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

theorem Coding.place_sub {a e j : ℕ} (h : a * mu g Φ ≤ e) : place (e, j) - a * (mu g Φ * 3) = (e - a * mu g Φ) * 3 + j := by sorry
