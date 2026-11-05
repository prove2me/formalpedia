-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Count_nSat_le
-- name    : ClauseBound.ParityChecks.Count.nSat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:50.529329+00:00
-- url     : https://prove2.me/theorems/ac765fc8-729a-44b9-9b3e-26bc3cda8fc6
-- title:
--   Count: n Sat le
-- statement:
--   At most 2^n assignments satisfy ψ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L121-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L121-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks

theorem ClauseBound.ParityChecks.Count.nSat_le (n : ℕ) (ψ : Fml) : nSat n ψ ≤ 2 ^ n := by sorry
