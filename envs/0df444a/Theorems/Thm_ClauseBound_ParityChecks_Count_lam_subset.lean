-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Count_lam_subset
-- name    : ClauseBound.ParityChecks.Count.lam_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:34.047673+00:00
-- url     : https://prove2.me/theorems/8d3c8a2f-0533-473d-8b81-9bc8fe9df8d1
-- title:
--   Count: lam subset
-- statement:
--   Without the current check every check is a subset of what it was.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L74-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L74-L80

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

theorem ClauseBound.ParityChecks.Count.lam_subset (m : ℕ) (Ls : List Chk) (cur : Chk) (j : ℕ) : lam m Ls j ⊆ lam m (Ls ++ [cur]) j := by sorry
