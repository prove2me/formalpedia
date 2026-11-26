-- Prove2me | Theorems.Thm_FD1D_transient_sqrt_term_le
-- name    : FD1D.transient_sqrt_term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:33:07.5838+00:00
-- url     : https://prove2.me/theorems/6632036c-e679-5b9f-ba51-846e81111a16
-- title:
--   FD1 D: transient sqrt term le
-- statement:
--   The FD1 D construction uses the transient sqrt term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L74-L90
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Arithmetic.lean#L74-L90

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Arithmetic
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.transient_sqrt_term_le
    {H T m : ℝ} (hm : 0 < m) (hT : m ^ 2 ≤ T)
    (hH0 : 1 / m ^ 2 ≤ H)
    (hH : H ≤ 206 / (3 * m ^ 2) + 1 / T) :
    Real.sqrt (H - 1 / m ^ 2) / Real.sqrt 6 ≤ 4 / m := by sorry
