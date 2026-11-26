-- Prove2me | Theorems.Thm_FD1D_harmonicPotential_nonneg
-- name    : FD1D.harmonicPotential_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:58.65813+00:00
-- url     : https://prove2.me/theorems/b0dcfff1-b557-491a-979b-b7fa206adf91
-- title:
--   FD1 D: harmonic Potential nonneg
-- statement:
--   The node potential is nonnegative when the regularization is positive.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L14-L20
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L14-L20

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators

theorem FD1D.harmonicPotential_nonneg {a : ℝ} (ha : 0 < a) (k : ℕ) :
    0 ≤ harmonicPotential a k := by sorry
