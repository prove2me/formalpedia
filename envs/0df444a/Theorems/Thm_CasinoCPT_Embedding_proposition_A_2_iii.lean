-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_proposition_A_2_iii
-- name    : CasinoCPT.Embedding.proposition_A_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:36.677317+00:00
-- url     : https://prove2.me/theorems/9c3d9ab7-524a-40bb-823d-d1608a6f9e20
-- title:
--   Proposition A.2 (iii), p. 45 — U^µ_t is convex in x and non-decreasing in t
-- statement:
--   Let $\mu\in\mathcal P_0(\mathbb Z)$ and $U_t=U^\mu_t$. Then $U_t(x)$ is convex in $x$ and non-decreasing in $t$:
--   $$2U_t(x)\le U_t(x-1)+U_t(x+1)\quad\forall x\in\mathbb Z,\qquad U_t(x)\le U_{t+1}(x)\quad\forall t\in\mathbb N,\ x\in\mathbb Z.$$
--
--   **Formalization Note.** The paper states convexity in $x\in\mathbb R$ of the piecewise-linear interpolation of $U_t$. A piecewise-linear interpolation of integer values is convex on $\mathbb R$ exactly when the values satisfy the discrete midpoint inequality above, so the integer form is equivalent. Monotonicity in $t$ is stated as `Monotone` in $t$ for each fixed $x$.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 45, Proposition A.2 (iii)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- Proposition A.2 (iii), p. 45: for `μ ∈ 𝒫₀(ℤ)`, `U^μ_t` is convex in `x` and non-decreasing
in `t`. Convexity of the piecewise-linear interpolation on `ℝ` is stated as discrete midpoint
convexity at the integers, which is equivalent. -/
theorem proposition_A_2_iii (μ : Measure ℤ) (hμ : InP0Z μ) :
    (∀ (t : ℕ) (x : ℤ), 2 * evol μ t x ≤ evol μ t (x - 1) + evol μ t (x + 1)) ∧
      ∀ x : ℤ, Monotone (fun t : ℕ => evol μ t x) := by sorry

end CasinoCPT.Embedding
