-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_TopOL_two_le_nbOf
-- name    : ClauseBound.ParityChecks.TopOL.two_le_nbOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:04.97444+00:00
-- url     : https://prove2.me/theorems/8c1b83a7-4b31-4412-bf31-bfd65a30c459
-- title:
--   Top OL: two le nb Of
-- statement:
--   nb ≥ 2 if 2·⌈log₂(2Δ)⌉ ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L53-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L53-L53

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

theorem ClauseBound.ParityChecks.TopOL.two_le_nbOf {n Δ : ℕ} (hΔ : 1 ≤ Δ) (h : 2 * LD Δ ≤ n) : 2 ≤ nbOf n Δ := by sorry
