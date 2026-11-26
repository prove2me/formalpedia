-- Prove2me | Theorems.Thm_FD1D_parameterA_cast_le_logb
-- name    : FD1D.parameterA_cast_le_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:06.658212+00:00
-- url     : https://prove2.me/theorems/2ba50094-2473-585b-8087-337240dfe09f
-- title:
--   FD1 D: parameter A cast le logb
-- statement:
--   A convenient explicit logarithmic bound, still written in base two.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L175-L206
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L175-L206

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.parameterA_cast_le_logb {m : ℕ} (hm : 2 ≤ m) :
    (parameterA m : ℝ) ≤ 800 * Real.logb 2 m := by sorry
