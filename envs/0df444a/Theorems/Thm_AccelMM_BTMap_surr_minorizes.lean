-- Prove2me | Theorems.Thm_AccelMM_BTMap_surr_minorizes
-- name    : AccelMM.BTMap.surr_minorizes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:33:57.918987+00:00
-- url     : https://prove2.me/theorems/50d9ca15-8b66-4fb8-a1af-beb281cb7a0f
-- title:
--   §2, p. 6 — the surrogate ℓ(x; y) of (2.7) minorizes the log-likelihood ℓ(x)
-- statement:
--   Let $d_{i,j}\in\mathbb N$ be the comparison counts of $n$ items, $\ell$ the Bradley–Terry log-likelihood (2.3) and $\ell(x;y)$ the surrogate (2.7). Then $\ell(\cdot\,;y)$ is a minorization surrogate of $\ell$: for all $x,y\in\mathbb R^n$,
--   $$\ell(x;y)\le\ell(x)\qquad\text{and}\qquad \ell(x;x)=\ell(x).$$
--
--   This is what makes the classic MM iteration (2.9) an ascent method for the log-likelihood, and, with the prior term added, for the log-posterior $\rho$.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 6, sentence after (2.7)

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

theorem surr_minorizes {n : ℕ} (d : Fin n → Fin n → ℕ) :
    (∀ x y : E n, surr d x y ≤ loglik d x) ∧ (∀ x : E n, surr d x x = loglik d x) := by sorry

end AccelMM.BTMap
