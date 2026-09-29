-- Prove2me | Theorems.Thm_CursoEDO_lipschitzInSecondVar_of_bounded_partial_deriv
-- name    : CursoEDO.lipschitzInSecondVar_of_bounded_partial_deriv
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T15:22:20.250683+00:00
-- url     : https://prove2.me/theorems/15ca3350-1aca-42a0-b0c9-b8a826d8b99e
-- title:
--   Proposição 2.1.4 — bounded partial derivative implies Lipschitz in the second variable
-- statement:
--   **A bounded partial derivative gives Lipschitz dependence on the second variable.**
--
--   Let $E_1, E_2, E_3$ be real normed spaces and let $U \subseteq E_1 \times E_2$ be open and convex.
--   Let $f : E_1 \times E_2 \to E_3$ be a map — not assumed continuous — and suppose that at every
--   point $p = (z,y) \in U$ the partial map $y' \mapsto f(z, y')$ is differentiable at $y$ with
--   derivative $\partial_2 f(p) \in \mathcal L(E_2, E_3)$, and that these partial derivatives are
--   uniformly bounded on $U$:
--
--   $$
--   \|\partial_2 f(p)\| \;\le\; c \qquad \text{for all } p \in U, \qquad c > 0 .
--   $$
--
--   Then $f$ is Lipschitz with respect to the second variable on $U$ with the same constant $c$:
--
--   $$
--   \|f(z,y_1) - f(z,y_2)\| \;\le\; c\,\|y_1-y_2\| \qquad \text{whenever } (z,y_1),(z,y_2) \in U .
--   $$
--
--   This is Proposição 2.1.4 of the source (p. 47). It is the practical criterion by which the
--   Lipschitz hypothesis of Picard's theorem is verified in examples: a $C^1$ right-hand side with
--   bounded state derivative on a convex domain satisfies it. Convexity of $U$ is what makes the mean
--   value inequality available along the segment joining $(z,y_1)$ to $(z,y_2)$.
-- source:
--   Augusto Armando de Castro Junior, Curso de Equacoes Diferenciais Ordinarias, lecture notes, 06 January 2009, p. 47, Proposicao 2.1.4

import Mathlib
import Definitions.Def_CursoEDO_Defs

namespace CursoEDO
theorem lipschitzInSecondVar_of_bounded_partial_deriv
    {E₁ E₂ E₃ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    (U : Set (E₁ × E₂)) (hUopen : IsOpen U) (hUconv : Convex ℝ U)
    (f : E₁ × E₂ → E₃) (f₂ : E₁ × E₂ → (E₂ →L[ℝ] E₃)) (c : ℝ) (hc : 0 < c)
    (hderiv : ∀ p ∈ U, HasFDerivAt (fun y : E₂ => f (p.1, y)) (f₂ p) p.2)
    (hbound : ∀ p ∈ U, ‖f₂ p‖ ≤ c) :
    LipschitzInSecondVar U f c := by sorry
end CursoEDO
