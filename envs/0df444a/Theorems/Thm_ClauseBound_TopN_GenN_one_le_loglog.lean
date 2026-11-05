-- Prove2me | Theorems.Thm_ClauseBound_TopN_GenN_one_le_loglog
-- name    : ClauseBound.TopN.GenN.one_le_loglog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:40:31.297026+00:00
-- url     : https://prove2.me/theorems/8bbe9a58-6c0c-4911-92cd-045f428915b7
-- title:
--   Gen N: one le loglog
-- statement:
--   1 ≤ log₂ log₂(n+4).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Gen.lean#L37-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Gen.lean#L37-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_End
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Gen
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.GenN
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN.Arith

theorem ClauseBound.TopN.GenN.one_le_loglog (n : ℕ) : (1 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) := by sorry
