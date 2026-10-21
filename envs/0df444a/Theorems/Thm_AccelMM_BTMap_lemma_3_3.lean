-- Prove2me | Theorems.Thm_AccelMM_BTMap_lemma_3_3
-- name    : AccelMM.BTMap.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:06.119991+00:00
-- url     : https://prove2.me/theorems/7b80f47f-2a9e-49f1-8c84-6d3df4bf013b
-- title:
--   Lemma 3.3, p. 9 — surrogate gap bound ℓ(x; y) − ℓ(x) ≥ −(δ/2)‖x − y‖² on [−ω, ω]ⁿ
-- statement:
--   Let $\omega\ge0$, let $d_{i,j}$ be the comparison counts with co-occurrence matrix $M$ and $d(M)=\|M\|_\infty$, and set
--   $$\delta=\tfrac12e^{2\omega}d(M).$$
--   Then for all $x,y\in[-\omega,\omega]^n$,
--   $$\ell(x;y)-\ell(x)\ge-\frac{\delta}{2}\|x-y\|^2,$$
--   where $\ell$ is the log-likelihood (2.3), $\ell(x;y)$ the surrogate (2.7), and $\|\cdot\|$ the Euclidean norm.
--
--   The bound measures how far the MM surrogate falls below the objective; $\delta$ enters every MM rate of the paper.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 9, Lemma 3.3

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

theorem lemma_3_3 {n : ℕ} (d : Fin n → Fin n → ℕ) (ω : ℝ) (hω : 0 ≤ ω)
    (x y : E n) (hx : x ∈ box ω) (hy : y ∈ box ω) :
    surr d x y - loglik d x ≥ -((1 / 2 * Real.exp (2 * ω) * degM d) / 2) * ‖x - y‖ ^ 2 := by sorry

end AccelMM.BTMap
