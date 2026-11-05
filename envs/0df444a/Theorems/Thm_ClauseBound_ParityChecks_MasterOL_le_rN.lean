-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_MasterOL_le_rN
-- name    : ClauseBound.ParityChecks.MasterOL.le_rN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:29:33.00774+00:00
-- url     : https://prove2.me/theorems/f78b927a-e7e8-407a-979d-88bb3c5eaa76
-- title:
--   Master OL: le r N
-- statement:
--   The function r is not too small: 1/(c·(log₂(n+2))^c) ≤ log₂ log₂(n+4)/(log₂(n+4))^α for α ≤ 1
--   and c ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/MasterOL.lean#L36-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/MasterOL.lean#L36-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_ClauseBound_ParityChecks_MasterOL
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.MasterOL
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.TopN.GenN

theorem ClauseBound.ParityChecks.MasterOL.le_rN {α : ℝ} {c : ℕ} (ha1 : α ≤ 1) (hc : 2 ≤ c) (n : ℕ) : 1 / ((c : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ c) ≤ SatK.rN 1 α n := by sorry
