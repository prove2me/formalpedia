-- Prove2me | Theorems.Thm_FD1D_m_le_two_mul_parameterA_mul_leafCount
-- name    : FD1D.m_le_two_mul_parameterA_mul_leafCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:12.829339+00:00
-- url     : https://prove2.me/theorems/e5b8f3e6-89b7-4a9d-8c16-2f432172ba2a
-- title:
--   FD1 D: m le two mul parameter A mul leaf Count
-- statement:
--   Natural-number form of the reciprocal leaf-size estimate.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L156-L163
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L156-L163

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.m_le_two_mul_parameterA_mul_leafCount {m : ℕ} (hm : 1 ≤ m) :
    m ≤ 2 * parameterA m * leafCount m := by sorry
