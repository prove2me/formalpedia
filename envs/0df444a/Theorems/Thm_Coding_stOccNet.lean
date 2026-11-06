-- Prove2me | Theorems.Thm_Coding_stOccNet
-- name    : Coding.stOccNet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:31:22.00848+00:00
-- url     : https://prove2.me/theorems/23c9d09e-4d9a-41c1-8400-9af067da2623
-- title:
--   Coding: st Occ Net
-- statement:
--   **Lean's network of Φ is the printed one with padding**: «A setting z_a of node a is a bit
--   string with one bit z_a[o] for each occurrence o in cluster a, and S_a is the set of all these bit
--   strings» (Section 6), where Lean's settings have one bit for each of the 3·m̄ places of a cluster.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L218-L241
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Occ.lean#L218-L241

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

theorem Coding.stOccNet : StOccNet := by sorry
