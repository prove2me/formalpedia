-- Prove2me | Theorems.Thm_Eight_two_le_of_le
-- name    : Eight.two_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:13:53.517262+00:00
-- url     : https://prove2.me/theorems/c02b263d-d737-43ac-8e60-21ce62a56e09
-- title:
--   Eight: two le of le
-- statement:
--   A number K ≥ 72/δ' with δ' ≤ 1/3 is at least 2 (even at least 216), as the definition of
--   «achievable» in the paper asks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Proof.lean#L60-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Proof.lean#L60-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_CountKSat_Value
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_Eight_SecProof_Proof
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog Paper

theorem Eight.two_le_of_le {δ' : ℝ} {K : ℕ} (hδ' : 0 < δ') (h3 : δ' ≤ 1 / 3) (hK : 72 / δ' ≤ K) : 2 ≤ K := by sorry
