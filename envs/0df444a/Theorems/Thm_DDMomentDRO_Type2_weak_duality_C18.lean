-- Prove2me | Theorems.Thm_DDMomentDRO_Type2_weak_duality_C18
-- name    : DDMomentDRO.Type2.weak_duality_C18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:13.262694+00:00
-- url     : https://prove2.me/theorems/b44c524f-2c78-415f-b144-65270b7aa381
-- title:
--   Proof of Theorem 2, p. 37 — weak duality between the inner LP (C-18) and the constraints (11b)
-- statement:
--   Fix a state $x$, support points $\xi^1,\dots,\xi^K\in\mathbb R^J$, next-stage values $Q^1(x),\dots,Q^K(x)$, a mean $\mu(x)\in\mathbb R^J$ and a matrix $\Sigma(x)\in\mathbb R^{J\times J}$. Let $p\in\mathcal P^{D_2}_{t+1}(x)$, that is, $p\ge0$, $\sum_kp_k=1$, $\sum_kp_k\xi^k=\mu(x)$ and $\sum_kp_k(\xi^k-\mu(x))(\xi^k-\mu(x))^\top=\Sigma(x)$. Let $s\in\mathbb R$, $u\in\mathbb R^J$ and $Y\in\mathbb R^{J\times J}$ satisfy (11b):
--   $$
--   s+u^\top\xi^k+(\xi^k-\mu(x))(\xi^k-\mu(x))^\top\bullet Y\ \ge\ Q^k(x)\qquad\text{for all }k\in[K].
--   $$
--   Then
--   $$
--   \sum_{k=1}^K p_kQ^k(x)\ \le\ s+u^\top\mu(x)+\Sigma(x)\bullet Y .
--   $$
--
--   This is the weak half of the LP duality that the proof of Theorem 2 uses: the dual variables $s,u,Y$ attached to the three equality constraints (C-18b)–(C-18d) give upper bounds on the inner maximization (C-18a).
--
--   **Formalization Note** $A\bullet B=\operatorname{trace}(A^\top B)$, written `(Aᵀ * B).trace`. The membership $p\in\mathcal P^{D_2}_{t+1}(x)$ includes $p\ge0$ (C-18e), which (10) as printed omits; without it the inequality fails.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 37, proof of Theorem 2, (C-18)

import Mathlib
import Definitions.Def_DDMomentDRO_Type2_Setting

namespace DDMomentDRO.Type2

open Matrix

theorem weak_duality_C18 {I J K : ℕ}
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (x : Fin I → ℝ) (p : Fin K → ℝ) (hp : p ∈ amb2 ξ μ Sig x)
    (s : ℝ) (u : Fin J → ℝ) (Y : Matrix (Fin J) (Fin J) ℝ)
    (hdual : ∀ k, Qn x k ≤ s + u ⬝ᵥ ξ k + ((vecMulVec (ξ k - μ x) (ξ k - μ x))ᵀ * Y).trace) :
    ∑ k, p k * Qn x k ≤ s + u ⬝ᵥ μ x + ((Sig x)ᵀ * Y).trace := by sorry

end DDMomentDRO.Type2
