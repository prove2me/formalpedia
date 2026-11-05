-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_log_pow_le
-- name    : ClauseBound.Alg.End.log_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:24:57.225666+00:00
-- url     : https://prove2.me/theorems/24209198-52df-449c-ba90-f77581113d50
-- title:
--   End: log pow le
-- statement:
--   (log₂(m+2))^j ≤ 3·j!·2^j·m for m ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L142-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L142-L160

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_CountKSat_InOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_ClauseBound_Alg_End
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat

theorem ClauseBound.Alg.End.log_pow_le (j : ℕ) {m : ℕ} (hm : 1 ≤ m) : Real.logb 2 ((m : ℝ) + 2) ^ j ≤ ((3 * j.factorial * 2 ^ j : ℕ) : ℝ) * m := by sorry
