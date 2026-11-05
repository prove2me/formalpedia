-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_ArithOL_stArithO
-- name    : ClauseBound.ParityChecks.ArithOL.stArithO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:23:24.537781+00:00
-- url     : https://prove2.me/theorems/4d8ca422-7e7c-408d-80e7-b933736923b9
-- title:
--   Arith OL: st Arith O
-- statement:
--   For c = `cO k C C₀` and every n₀: with l the level picked for n and s = s(l), the exponent of
--   the pad is at most A·n·e_l·(s+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L570-L599
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ArithOL.lean#L570-L599

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith

theorem ClauseBound.ParityChecks.ArithOL.stArithO : StArithO := by sorry
