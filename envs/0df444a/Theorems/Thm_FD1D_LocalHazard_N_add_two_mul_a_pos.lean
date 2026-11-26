-- Prove2me | Theorems.Thm_FD1D_LocalHazard_N_add_two_mul_a_pos
-- name    : FD1D.LocalHazard.N_add_two_mul_a_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:51:57.206568+00:00
-- url     : https://prove2.me/theorems/21ca8982-7e97-5e49-a86d-8bca391c6c8b
-- title:
--   Local Hazard: N add two mul a pos
-- statement:
--   The Local Hazard construction uses the N add two mul a pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L101-L104
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L101-L104

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.N_add_two_mul_a_pos {a : ℝ} (ha : 0 < a) (x y : ℕ) :
    0 < N x y + 2 * a := by sorry
