-- Prove2me | Theorems.Thm_FD1D_bellman_global_bound
-- name    : FD1D.bellman_global_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:47.903503+00:00
-- url     : https://prove2.me/theorems/25b67655-f506-45c6-a048-c885fda49249
-- title:
--   FD1 D: bellman global bound
-- statement:
--   Global form of the local Bellman inequality (7).  This is the telescope used
--   immediately before equation (9).
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L554-L610
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L554-L610

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.bellman_global_bound
    (L : ℕ) (h t Z B : ∀ d, DyadicNode d → ℝ)
    (hlocal : ∀ d, d < L → ∀ v,
      childAverage (fun d v => t d v * Z d v) d v +
          childAverage B d v - B d v ≥
        (childAverage (fun d v => (h d v) ^ 2) d v - (h d v) ^ 2) / 100) :
    nonrootWeightedSum (fun d v => t d v * Z d v) L ≥
      (hazardEnergy h L - hazardEnergy h 0) / 100 +
        B 0 dyadicRoot - weightedLevel B L := by sorry
