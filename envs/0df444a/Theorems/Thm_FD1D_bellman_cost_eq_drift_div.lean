-- Prove2me | Theorems.Thm_FD1D_bellman_cost_eq_drift_div
-- name    : FD1D.bellman_cost_eq_drift_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:33.000625+00:00
-- url     : https://prove2.me/theorems/3b4704b5-3181-5917-b3ef-6cf672098710
-- title:
--   FD1 D: bellman cost eq drift div
-- statement:
--   The FD1 D construction uses the bellman cost eq drift div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L622-L635
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L622-L635

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.bellman_cost_eq_drift_div
    (L : ℕ) (a : ℝ)
    (N q t Z : ∀ d, DyadicNode d → ℝ)
    (ht : ∀ d v, t d v = (nodeMass d v - q d v) / a)
    (hZ : ∀ d v, Z d v = nodeMass d v / (N d v + a)) :
    nonrootWeightedSum (fun d v => t d v * Z d v) L =
      bellmanDrift L a N q / a := by sorry
