-- Prove2me | Theorems.Thm_FD1D_V5_parameterQuotient_lt_two_mul_leafCount
-- name    : FD1D.V5.parameterQuotient_lt_two_mul_leafCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:56.182289+00:00
-- url     : https://prove2.me/theorems/d7b0542f-7716-5c0d-a1dc-b4ed7fbdd72c
-- title:
--   V5: parameter Quotient lt two mul leaf Count
-- statement:
--   The V5 construction uses the parameter Quotient lt two mul leaf Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L91-L94
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/Parameters.lean#L91-L94

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics

theorem FD1D.V5.parameterQuotient_lt_two_mul_leafCount (m : ℕ) :
    m / parameterA m < 2 * leafCount m := by sorry
