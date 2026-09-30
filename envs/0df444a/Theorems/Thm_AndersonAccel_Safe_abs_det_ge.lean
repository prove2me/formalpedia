-- Prove2me | Theorems.Thm_AndersonAccel_Safe_abs_det_ge
-- name    : AndersonAccel.Safe.abs_det_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:06:35.363983+00:00
-- url     : https://prove2.me/theorems/62240be3-8b35-45c9-bf2c-91cfad39efaa
-- title:
--   Lemma 3.2 — Powell-regularized updates keep $|\det B_k|\ge\bar\theta^{m_k}>0$
-- statement:
--   Let $\bar\theta\in(0,1)$, let $s_0,\dots,s_{m_k-1}$ and $y_0,\dots,y_{m_k-1}$ be arbitrary vectors in $\mathbb R^n$, and let $B^0=I,\dots,B^{m_k}$ be the Powell-regularized rank-one matrices of (3.5), with $\hat s_i$ the orthogonalization (3.2) and $\tilde y_i$ as in (3.3). Suppose every update is well-defined, i.e. $\hat s_i^Ts_i\neq0$ for $i=0,\dots,m_k-1$. Then
--   $$|\det(B_k)|\ \ge\ \bar\theta^{\,m_k}\ >\ 0,\qquad B_k=B^{m_k},$$
--   and in particular $B_k$ is invertible.
--
--   This is the nonsingularity result for the modified quasi-Newton matrices; it shows how the parameter $\bar\theta$ trades stability against the size of each update.
--
--   **Formalization Note** $\det$ is `LinearMap.det` of the continuous linear map; invertibility is `IsUnit` in the ring of continuous linear maps. The window is re-indexed to start at $0$ (the paper's $s_{k-m_k},\dots,s_{k-1}$).
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3176, Lemma 3.2

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic
import Definitions.Def_AndersonAccel_Safe_windowB

namespace AndersonAccel.Safe

/-- Lemma 3.2 (p. 3176). If every update of (3.5) is well-defined (`ŝ_iᵀ s_i ≠ 0`), then
`|det B| ≥ θ̄^{m_k} > 0` and `B` is invertible. -/
theorem abs_det_ge {n : ℕ} (θbar : ℝ) (hθ0 : 0 < θbar) (hθ1 : θbar < 1)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (mk : ℕ)
    (hwd : ∀ i < mk, inner ℝ (windowShat s i) (s i) ≠ 0) :
    θbar ^ mk ≤ |LinearMap.det (windowB θbar s y mk :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| ∧
      0 < θbar ^ mk ∧ IsUnit (windowB θbar s y mk) := by sorry

end AndersonAccel.Safe
