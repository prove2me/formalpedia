-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_TopOL_LD_pos
-- name    : ClauseBound.ParityChecks.TopOL.LD_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:29:49.226496+00:00
-- url     : https://prove2.me/theorems/0ed3447a-1de3-42fb-a033-dae7f4d9a58e
-- title:
--   Top OL: LD pos
-- statement:
--   ⌈log₂(2Δ)⌉ ≥ 1 for Δ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L50-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L50-L50

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

theorem ClauseBound.ParityChecks.TopOL.LD_pos {Δ : ℕ} (h : 1 ≤ Δ) : 0 < LD Δ := by sorry
