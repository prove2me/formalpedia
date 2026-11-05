-- Prove2me | Theorems.Thm_Coding_length_occIn_le
-- name    : Coding.length_occIn_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:05:55.530867+00:00
-- url     : https://prove2.me/theorems/d1c20ce3-50b0-414b-80c8-f4d518088b11
-- title:
--   Coding: length occ In le
-- statement:
--   There are at most 3 occurrences for each clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccMore.lean#L38-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccMore.lean#L38-L47

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
variable {g : ℕ} {Φ : Fml}

theorem Coding.length_occIn_le (h3 : ∀ C ∈ Φ, C.length ≤ 3) (e₀ r : ℕ) : (occIn Φ e₀ r).length ≤ 3 * r := by sorry
