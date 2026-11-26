-- Prove2me | Theorems.Thm_FD1D_V5_LocalPolicy_bias_eq_massLeft_sub_massRight
-- name    : FD1D.V5.LocalPolicy.bias_eq_massLeft_sub_massRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:34:35.869388+00:00
-- url     : https://prove2.me/theorems/9e49e35c-76f1-4ba4-a7e3-92da8cae8fc7
-- title:
--   Local Policy: bias eq mass Left sub mass Right
-- statement:
--   The Local Policy construction uses the bias eq mass Left sub mass Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalPolicy.lean#L159-L163
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalPolicy.lean#L159-L163

import Definitions.Def_FD1D_V5_Parameters
import Definitions.Def_FD1D_V5_LocalPolicy
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section

theorem FD1D.V5.LocalPolicy.bias_eq_massLeft_sub_massRight (a p h : ℝ) (x y : ℕ) :
    bias a p h x y =
      massLeft a p h x y - massRight a p h x y := by sorry
