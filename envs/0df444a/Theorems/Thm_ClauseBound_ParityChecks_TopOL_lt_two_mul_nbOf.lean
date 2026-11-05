-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_TopOL_lt_two_mul_nbOf
-- name    : ClauseBound.ParityChecks.TopOL.lt_two_mul_nbOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:06.111171+00:00
-- url     : https://prove2.me/theorems/f4a4ec77-32b1-487e-b9af-dfc184a09cac
-- title:
--   Top OL: lt two mul nb Of
-- statement:
--   n < 2·nb·⌈log₂(2Δ)⌉ if nb ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L56-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L56-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (theta bsum leafC)
open PaddedDescent.F.Mark (WfL occ nSat)

theorem ClauseBound.ParityChecks.TopOL.lt_two_mul_nbOf {n Δ : ℕ} (hΔ : 1 ≤ Δ) (h : 1 ≤ nbOf n Δ) : n < 2 * (nbOf n Δ * LD Δ) := by sorry
