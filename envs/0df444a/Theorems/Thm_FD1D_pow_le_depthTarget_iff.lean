-- Prove2me | Theorems.Thm_FD1D_pow_le_depthTarget_iff
-- name    : FD1D.pow_le_depthTarget_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:46.367562+00:00
-- url     : https://prove2.me/theorems/2bebe5c4-ea12-4217-8ff4-4c17681c94cc
-- title:
--   FD1 D: pow le depth Target iff
-- statement:
--   Exponent form of the fact that `n` is the largest admissible power of two.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L132-L134
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L132-L134

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.pow_le_depthTarget_iff {m k : ℕ} :
    2 ^ k ≤ depthTarget m ↔ k ≤ treeDepth m := by sorry
