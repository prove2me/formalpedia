-- Prove2me | Theorems.Thm_FD1D_deterministic_bellman_bound
-- name    : FD1D.deterministic_bellman_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:50:30.017407+00:00
-- url     : https://prove2.me/theorems/4ed3b9ff-9ca1-42a0-a771-ed372c243b70
-- title:
--   FD1 D: deterministic bellman bound
-- statement:
--   The deterministic Bellman estimate (9).  The hypotheses are exactly the
--   local certificate (7), the definitions of `t` and `Z`, and the terminal/root
--   sign bounds proved in the paper.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L642-L682
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L642-L682

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.deterministic_bellman_bound
    (L : ℕ) {a m : ℝ} (N q h t Z B : ∀ d, DyadicNode d → ℝ)
    (ha : 0 < a) (hm : 0 < m)
    (ht : ∀ d v, t d v = (nodeMass d v - q d v) / a)
    (hZ : ∀ d v, Z d v = nodeMass d v / (N d v + a))
    (hroot : h 0 dyadicRoot = 1 / m)
    (hlocal : ∀ d, d < L → ∀ v,
      childAverage (fun d v => t d v * Z d v) d v +
          childAverage B d v - B d v ≥
        (childAverage (fun d v => (h d v) ^ 2) d v -
          (h d v) ^ 2) / 100)
    (hleaf : ∀ v : DyadicNode L, B L v ≤ 0)
    (hBroot : -(1 / (3 * m ^ 2)) ≤ B 0 dyadicRoot) :
    bellmanDrift L a N q ≥
      a * (hazardEnergy h L / 100 - 103 / (300 * m ^ 2)) := by sorry
