-- Prove2me | Theorems.Thm_FD1D_depthTarget_ne_zero
-- name    : FD1D.depthTarget_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:50.30757+00:00
-- url     : https://prove2.me/theorems/c5c5f9ac-4522-5710-a129-6522b5935f32
-- title:
--   FD1 D: depth Target ne zero
-- statement:
--   The FD1 D construction uses the depth Target ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L70-L72
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Parameters.lean#L70-L72

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics

theorem FD1D.depthTarget_ne_zero (m : ℕ) :
    depthTarget m ≠ 0 := by sorry
