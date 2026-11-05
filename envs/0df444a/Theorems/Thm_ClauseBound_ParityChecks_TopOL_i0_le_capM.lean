-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_TopOL_i0_le_capM
-- name    : ClauseBound.ParityChecks.TopOL.i0_le_capM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:26.327142+00:00
-- url     : https://prove2.me/theorems/3afdbf4b-c70f-429f-9c5f-db7d87a6f757
-- title:
--   Top OL: i0 le cap M
-- statement:
--   i₀ is at most the cap, for n ≥ 2^20.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L63-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/TopOL.lean#L63-L71

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

theorem ClauseBound.ParityChecks.TopOL.i0_le_capM {n : ℕ} (hn : 2 ^ 20 ≤ n) (Δ m : ℕ) : (parOf n Δ m).i₀ ≤ capM (parOf n Δ m) := by sorry
