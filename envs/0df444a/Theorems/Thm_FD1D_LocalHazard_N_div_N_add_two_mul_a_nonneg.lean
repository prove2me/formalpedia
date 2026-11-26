-- Prove2me | Theorems.Thm_FD1D_LocalHazard_N_div_N_add_two_mul_a_nonneg
-- name    : FD1D.LocalHazard.N_div_N_add_two_mul_a_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:53.303889+00:00
-- url     : https://prove2.me/theorems/55c12814-b999-56f6-bdf9-209f2dfa1fe7
-- title:
--   Local Hazard: N div N add two mul a nonneg
-- statement:
--   The Local Hazard construction uses the N div N add two mul a nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L365-L367
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean#L365-L367

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard

theorem FD1D.LocalHazard.N_div_N_add_two_mul_a_nonneg {a : ℝ} (ha : 0 < a) (x y : ℕ) :
    0 ≤ N x y / (N x y + 2 * a) := by sorry
