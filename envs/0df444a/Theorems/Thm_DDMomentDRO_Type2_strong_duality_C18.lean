-- Prove2me | Theorems.Thm_DDMomentDRO_Type2_strong_duality_C18
-- name    : DDMomentDRO.Type2.strong_duality_C18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:20.891191+00:00
-- url     : https://prove2.me/theorems/e70c5de9-9d90-4dd8-83b4-dc225b2d71c0
-- title:
--   Proof of Theorem 2, p. 37 — if (C-18) is feasible, its maximum is attained and equals the attained minimum of its LP dual
-- statement:
--   Fix a state $x$, support points $\xi^1,\dots,\xi^K\in\mathbb R^J$, next-stage values $Q^1(x),\dots,Q^K(x)$, a mean $\mu(x)$ and a matrix $\Sigma(x)$, and suppose the Type 2 ambiguity set $\mathcal P^{D_2}_{t+1}(x)$ (the feasible set of the linear program (C-18)) is nonempty. Then there are $p^\ast\in\mathcal P^{D_2}_{t+1}(x)$ and $(s^\ast,u^\ast,Y^\ast)\in\mathbb R\times\mathbb R^J\times\mathbb R^{J\times J}$ satisfying (11b),
--   $$
--   s^\ast+u^{\ast\top}\xi^k+(\xi^k-\mu(x))(\xi^k-\mu(x))^\top\bullet Y^\ast\ \ge\ Q^k(x)\qquad\text{for all }k,
--   $$
--   with equal objective values:
--   $$
--   \sum_{k=1}^K p^\ast_kQ^k(x)\ =\ s^\ast+u^{\ast\top}\mu(x)+\Sigma(x)\bullet Y^\ast .
--   $$
--
--   Together with weak duality this says that the maximum of (C-18) is attained at $p^\ast$, the minimum of its dual is attained at $(s^\ast,u^\ast,Y^\ast)$, and the two optimal values coincide. This is the strong-duality step that lets the proof of Theorem 2 replace the inner maximization of (2) by a minimization.
--
--   **Formalization Note** $A\bullet B=\operatorname{trace}(A^\top B)$, written `(Aᵀ * B).trace`. $Y$ is an unrestricted real $J\times J$ matrix. The feasible set includes $p\ge0$ (C-18e).
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 37, proof of Theorem 2, (C-18)

import Mathlib
import Definitions.Def_DDMomentDRO_Type2_Setting

namespace DDMomentDRO.Type2

open Matrix

theorem strong_duality_C18 {I J K : ℕ}
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (x : Fin I → ℝ) (hne : (amb2 ξ μ Sig x).Nonempty) :
    ∃ p ∈ amb2 ξ μ Sig x, ∃ s : ℝ, ∃ u : Fin J → ℝ, ∃ Y : Matrix (Fin J) (Fin J) ℝ,
      (∀ k, Qn x k ≤ s + u ⬝ᵥ ξ k + ((vecMulVec (ξ k - μ x) (ξ k - μ x))ᵀ * Y).trace) ∧
      ∑ k, p k * Qn x k = s + u ⬝ᵥ μ x + ((Sig x)ᵀ * Y).trace := by sorry

end DDMomentDRO.Type2
