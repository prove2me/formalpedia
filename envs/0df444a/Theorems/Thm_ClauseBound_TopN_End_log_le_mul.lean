-- Prove2me | Theorems.Thm_ClauseBound_TopN_End_log_le_mul
-- name    : ClauseBound.TopN.End.log_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:21:49.565795+00:00
-- url     : https://prove2.me/theorems/8c2b64d6-1f33-45b6-93f6-fd090d66c65a
-- title:
--   End: log le mul
-- statement:
--   log₂(n+2) ≤ c·D·(n·r), where D = 3·(c+1)!·2^(c+1), if r ≥ 1/(c·(log₂(n+2))^c) and n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/End.lean#L27-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/End.lean#L27-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_WidthK_Decode
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_TopN_End
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End

theorem ClauseBound.TopN.End.log_le_mul {c n : ℕ} {r : ℝ} (hc : 1 ≤ c) (hn : 1 ≤ n) (h : 1 / ((c : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ c) ≤ r) :
    Real.logb 2 ((n : ℝ) + 2) ≤ ((c * (3 * (c + 1).factorial * 2 ^ (c + 1)) : ℕ) : ℝ) * ((n : ℝ) * r) := by sorry
