-- Prove2me | Theorems.Thm_FD1D_harmonicPotential_zero
-- name    : FD1D.harmonicPotential_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:51:34.61642+00:00
-- url     : https://prove2.me/theorems/5b404d8f-d376-42fd-b31a-17f50e730f4f
-- title:
--   FD1 D: harmonic Potential zero
-- statement:
--   The FD1 D construction uses the harmonic Potential zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L20-L22
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Drift.lean#L20-L22

import Definitions.Def_FD1D_Arithmetic
import Definitions.Def_FD1D_Drift
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.harmonicPotential_zero (a : ℝ) :
    harmonicPotential a 0 = 0 := by sorry
