-- Prove2me | Theorems.Thm_FD1D_V5_LocalBellman_Normalized_floorJ_bound
-- name    : FD1D.V5.LocalBellman.Normalized.floorJ_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:26:59.723854+00:00
-- url     : https://prove2.me/theorems/155a93d1-d20d-4623-a87d-758accedb68f
-- title:
--   Normalized: floor J bound
-- statement:
--   The Normalized construction uses the floor J bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L951-L956
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean#L951-L956

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized

theorem FD1D.V5.LocalBellman.Normalized.floorJ_bound
    {K e : ℝ} (hK : 1 ≤ K) (he0 : 0 ≤ e) :
    (K ^ 2 + e ^ 2) / 4 ≤ floorJ K e := by sorry
