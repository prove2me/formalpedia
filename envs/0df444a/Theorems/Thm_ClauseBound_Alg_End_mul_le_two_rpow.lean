-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_mul_le_two_rpow
-- name    : ClauseBound.Alg.End.mul_le_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:11:53.978337+00:00
-- url     : https://prove2.me/theorems/a4b9694e-14bd-4bd2-a92b-5bde7acc2046
-- title:
--   End: mul le two rpow
-- statement:
--   k·m ≤ 2^(2·c·D·k·m·r), where D = 3·(c+1)!·2^(c+1), if r ≥ 1/(c·(log₂(m+2))^c).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L170-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L170-L198

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

theorem ClauseBound.Alg.End.mul_le_two_rpow {c k m : ℕ} {r : ℝ} (hc : 1 ≤ c) (hk : 1 ≤ k) (hm : 1 ≤ m) (h : 1 / ((c : ℝ) * Real.logb 2 ((m : ℝ) + 2) ^ c) ≤ r) :
    ((k * m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * c * (3 * (c + 1).factorial * 2 ^ (c + 1)) : ℕ) : ℝ) * ((k : ℝ) * m * r)) := by sorry
