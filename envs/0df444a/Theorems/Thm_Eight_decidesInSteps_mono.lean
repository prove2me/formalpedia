-- Prove2me | Theorems.Thm_Eight_decidesInSteps_mono
-- name    : Eight.decidesInSteps_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:14:23.611143+00:00
-- url     : https://prove2.me/theorems/0eb17735-a0a1-42cc-a13d-6501e3d33abd
-- title:
--   Eight: decides In Steps mono
-- statement:
--   A machine that decides 3-SAT within c·2^{δn} steps does so within c·2^{δ₁n} steps for every δ₁ ≥
--   δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Proof.lean#L66-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Proof.lean#L66-L72

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

theorem Eight.decidesInSteps_mono {Ms : StepMachine (List Bool) Bool} {δ δ₁ : ℝ} (h : Paper.DecidesInSteps Ms δ) (hle : δ ≤ δ₁) : Paper.DecidesInSteps Ms δ₁ := by sorry
