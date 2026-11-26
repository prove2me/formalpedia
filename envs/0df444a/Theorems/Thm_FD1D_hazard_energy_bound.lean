-- Prove2me | Theorems.Thm_FD1D_hazard_energy_bound
-- name    : FD1D.hazard_energy_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:48:45.136159+00:00
-- url     : https://prove2.me/theorems/1ac5b339-4281-5647-a5fb-0b58cf54a985
-- title:
--   FD1 D: hazard energy bound
-- statement:
--   Summing the local hazard inequality gives equation (2), before substituting
--   the root value `h_root = 1/m`.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L448-L483
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L448-L483

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.hazard_energy_bound
    (L : ℕ) (a : ℝ)
    (h b : ∀ d, DyadicNode d → ℝ)
    (hlocal : ∀ d, d < L → ∀ v,
      (b d v) ^ 2 ≤ 2 * a ^ 2 *
        (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2)) :
    internalWeightedSum (fun d v => (b d v) ^ 2) L ≤
      2 * a ^ 2 * (hazardEnergy h L - hazardEnergy h 0) := by sorry
