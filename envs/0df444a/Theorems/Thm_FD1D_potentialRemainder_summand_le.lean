-- Prove2me | Theorems.Thm_FD1D_potentialRemainder_summand_le
-- name    : FD1D.potentialRemainder_summand_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:29.745743+00:00
-- url     : https://prove2.me/theorems/ee40d85f-c58d-4c59-b52e-2150dd8bcfad
-- title:
--   FD1 D: potential Remainder summand le
-- statement:
--   Every summand of `R` is at most `p_v h_v²`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L140-L145
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Potential.lean#L140-L145

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_Drift
import Definitions.Def_FD1D_Potential
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators

theorem FD1D.potentialRemainder_summand_le
    {a N q h p : ℝ}
    (hp : 0 ≤ p) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (haN : 0 < N + a) (hmajor : p ≤ (N + a) * h) :
    p ^ 3 * (1 - q) / ((N + a) * (N + a + 1)) ≤ p * h ^ 2 := by sorry
