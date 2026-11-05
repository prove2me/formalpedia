-- Prove2me | Theorems.Thm_ClauseBound_TopN_GenN_log_four_le
-- name    : ClauseBound.TopN.GenN.log_four_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:20.138822+00:00
-- url     : https://prove2.me/theorems/aabf4af6-da9b-416e-9f62-14fe481794da
-- title:
--   Gen N: log four le
-- statement:
--   log₂(n+4) ≤ 2·log₂(n+2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Gen.lean#L43-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Gen.lean#L43-L47

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

theorem ClauseBound.TopN.GenN.log_four_le (n : ℕ) : Real.logb 2 ((n : ℝ) + 4) ≤ 2 * Real.logb 2 ((n : ℝ) + 2) := by sorry
