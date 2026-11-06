-- Prove2me | Theorems.Thm_Coding_abs_boole_lt
-- name    : Coding.abs_boole_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:06:23.815354+00:00
-- url     : https://prove2.me/theorems/37258ad2-f278-4475-aa27-2980a3fd048e
-- title:
--   Coding: abs boole lt
-- statement:
--   |[p]| < 2^B with B = 1, as condition (ii) of Definition 2 asks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccMore.lean#L53-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccMore.lean#L53-L53

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

theorem Coding.abs_boole_lt (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| < 2 ^ 1 := by sorry
