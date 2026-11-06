-- Prove2me | Theorems.Thm_Coding_boole_zero_or_one
-- name    : Coding.boole_zero_or_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:03:50.390305+00:00
-- url     : https://prove2.me/theorems/786eb98a-8885-4139-82d0-cc460b1b88f8
-- title:
--   Coding: boole zero or one
-- statement:
--   [p] is 0 or 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccMore.lean#L50-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccMore.lean#L50-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Occ
import Definitions.Def_Coding_Padding
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Coding_OccMore
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}

theorem Coding.boole_zero_or_one (p : Prop) [Decidable p] : (if p then (1 : ℤ) else 0) = 0 ∨ (if p then (1 : ℤ) else 0) = 1 := by sorry
