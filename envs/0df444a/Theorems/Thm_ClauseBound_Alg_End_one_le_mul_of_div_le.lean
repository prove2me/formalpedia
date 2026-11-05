-- Prove2me | Theorems.Thm_ClauseBound_Alg_End_one_le_mul_of_div_le
-- name    : ClauseBound.Alg.End.one_le_mul_of_div_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:47:17.262703+00:00
-- url     : https://prove2.me/theorems/ea765ed5-244f-4132-8958-6503aa444639
-- title:
--   End: one le mul of div le
-- statement:
--   If r ≥ 1/(c·y^c) with c ≥ 1 and y ≥ 1 then c·y^c·r ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L163-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/End.lean#L163-L167

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

theorem ClauseBound.Alg.End.one_le_mul_of_div_le {c : ℕ} {y r : ℝ} (hc : 1 ≤ c) (hy : 1 ≤ y) (h : 1 / ((c : ℝ) * y ^ c) ≤ r) : 1 ≤ (c : ℝ) * y ^ c * r := by sorry
