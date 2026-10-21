-- Prove2me | Theorems.Thm_AccelMM_BTMap_lamMax_le_two_degM
-- name    : AccelMM.BTMap.lamMax_le_two_degM
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:18.231857+00:00
-- url     : https://prove2.me/theorems/259d8463-d869-46ef-a63b-90882a2cb7eb
-- title:
--   §3.2, p. 8 — Gershgorin bound λ_n(L_M) ≤ 2d(M)
-- statement:
--   For the comparison counts $d_{i,j}$ with co-occurrence matrix $M$, the largest eigenvalue of the Laplacian $L_M=D_M-M$ is at most twice the maximum row sum of $M$:
--   $$\lambda_n(L_M)\le2\,d(M).$$
--
--   This lets the paper replace $\lambda_n(L_M)$ by the more interpretable $d(M)$, the maximum number of comparisons of an item, in all smoothness constants.
--
--   **Formalization Note** For $n=0$ both sides are $0$ by convention.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 8, §3.2

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

theorem lamMax_le_two_degM {n : ℕ} (d : Fin n → Fin n → ℕ) : lamMax d ≤ 2 * degM d := by sorry

end AccelMM.BTMap
