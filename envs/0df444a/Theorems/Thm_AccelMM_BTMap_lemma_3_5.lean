-- Prove2me | Theorems.Thm_AccelMM_BTMap_lemma_3_5
-- name    : AccelMM.BTMap.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:33:56.70189+00:00
-- url     : https://prove2.me/theorems/fec85173-8503-44d7-b9d8-967ee8992b56
-- title:
--   Lemma 3.5, p. 10 — the same gap bound for the MAP surrogate ρ(x; y)
-- statement:
--   Let $\omega\ge0$, $\alpha,\beta\in\mathbb R$, $d_{i,j}$ the comparison counts and $\delta=\tfrac12e^{2\omega}d(M)$. For all $x,y\in[-\omega,\omega]^n$,
--   $$\rho(x;y)-\rho(x)\ge-\frac{\delta}{2}\|x-y\|^2,$$
--   where $\rho=\ell+\ell_0$ is the log-a posteriori function (2.4) and $\rho(x;y)=\ell(x;y)+\ell_0(x)$ its MM surrogate.
--
--   This is the surrogate condition of Theorem 4.2 for $f=-\rho$ and $g=-\rho(\cdot\,;\cdot)$, restricted to $W_\omega$.
--
--   **Formalization Note** The page states the lemma for all $x,y\in[-\omega,\omega]^n$; the hypothesis $\omega\ge0$ is carried over from Lemma 3.3, from which it follows.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 10, Lemma 3.5

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

theorem lemma_3_5 {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ) (hω : 0 ≤ ω)
    (x y : E n) (hx : x ∈ box ω) (hy : y ∈ box ω) :
    rhoSurr α β d x y - rho α β d x ≥
      -((1 / 2 * Real.exp (2 * ω) * degM d) / 2) * ‖x - y‖ ^ 2 := by sorry

end AccelMM.BTMap
