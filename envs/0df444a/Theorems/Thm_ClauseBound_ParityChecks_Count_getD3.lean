-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Count_getD3
-- name    : ClauseBound.ParityChecks.Count.getD3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:44.875774+00:00
-- url     : https://prove2.me/theorems/7edbe68c-0ce9-4587-83f5-10f822b52f4f
-- title:
--   Count: get D3
-- statement:
--   Three numbers that are at most c, as a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L102-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L102-L107

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

theorem ClauseBound.ParityChecks.Count.getD3 {a b d c : ℕ} (ha : a ≤ c) (hb : b ≤ c) (hd : d ≤ c) : ∀ l < 3, [a, b, d].getD l 0 ≤ c := by sorry
