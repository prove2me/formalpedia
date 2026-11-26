-- Prove2me | Theorems.Thm_FD1D_parameterQuotient_lt_two_mul_leafCount
-- name    : FD1D.parameterQuotient_lt_two_mul_leafCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:57.996816+00:00
-- url     : https://prove2.me/theorems/6c3e15b2-1248-4516-b216-51b02aa8b2b1
-- title:
--   FD1 D: parameter Quotient lt two mul leaf Count
-- statement:
--   The FD1 D construction uses the parameter Quotient lt two mul leaf Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L150-L153
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L150-L153

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.parameterQuotient_lt_two_mul_leafCount (m : ℕ) :
    m / parameterA m < 2 * leafCount m := by sorry
