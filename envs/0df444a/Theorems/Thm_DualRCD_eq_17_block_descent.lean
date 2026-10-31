-- Prove2me | Theorems.Thm_DualRCD_eq_17_block_descent
-- name    : DualRCD.eq_17_block_descent
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:21.221853+00:00
-- url     : https://prove2.me/theorems/cae293b2-d1d1-47ba-9ffd-68dd38b0d835
-- title:
--   (17) — block descent inequality for $\tilde d$
-- statement:
--   Let $g$ be $1$-strongly convex. For every $y\in\mathbb R^{mn}$, every block $i$ and every $t_i\in\mathbb R^n$,
--   $$
--   \tilde d(y+U_it_i)\le\tilde d(y)+\langle\nabla_i\tilde d(y),t_i\rangle+\frac12\|t_i\|^2 ,
--   $$
--   where $\nabla_i\tilde d(y)=-\nabla g^*(-\sum_jy_j)$.
--
--   This is the block descent inequality for the smooth part of the dual: each block has Lipschitz constant $L_i=1$, which is why the RCD step uses no step size.
--
--   **Formalization Note.** $\nabla g^*(-\sum_jy_j)$ is written as the arg max $x$ of $\langle-\sum_jy_j,\cdot\rangle-g$, and the inequality is in the extended reals, with both values of $\tilde d$ finite.
--
--   Differences from the source:
--   - encoding: ∇_i d̃(y) = −∇g*(−Σ_j y_j) → −x for an arg max x of ⟨−Σ_j y_j, ·⟩ − g (IsConjMaximizer); reason: the paper's own formula on p.15; the arg max is unique for strongly convex g
--   - encoding: d̃ real-valued → dTilde valued in EReal, the inequality in EReal; reason: the published conjugate is EReal-valued; d̃ is finite for strongly convex g
--   - encoding: g 1-strongly convex → IsStronglyConvexGrad 1 g, with Differentiable ℝ g and Mathlib's gradient; reason: Lean's gradient is 0 where g is not differentiable, so differentiability is stated
--   - encoding: ℝ^{mn} with the Euclidean norm → PiLp 2 of EuclideanSpace ℝ (Fin n) (DualSpace n m); reason: Lean convention; ‖y‖² = Σᵢ‖yᵢ‖² is the paper's norm
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §4, p.14, display (17)

import Mathlib
import Definitions.Def_DualRCD_IsStronglyConvexGrad
import Definitions.Def_DualRCD_IsConjMaximizer
import Definitions.Def_DualRCD_blockInj
import Definitions.Def_DualRCD_dTilde

open scoped RealInnerProductSpace

namespace DualRCD

/-- The block descent inequality (17) of Necoara & Fercoq, arXiv:1911.06014v1, §4, p.14:
`d̃(y + Uᵢ tᵢ) ≤ d̃(y) + ⟨∇ᵢ d̃(y), tᵢ⟩ + ½‖tᵢ‖²` for all `tᵢ ∈ ℝⁿ`, for `g` `1`-strongly convex.

**Formalization Note.** `∇ᵢ d̃(y) = −∇g*(−Σⱼ yⱼ) = −x`, where `x` is the arg max of
`⟨−Σⱼ yⱼ, ·⟩ − g` (pp.14–15). The inequality is in `EReal`; both values of `d̃` are finite for
strongly convex `g`. -/
theorem eq_17_block_descent {n m : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : IsStronglyConvexGrad 1 g) (y : DualSpace n m) (i : Fin m)
    (t x : EuclideanSpace ℝ (Fin n)) (hx : IsConjMaximizer g (-∑ j, y j) x) :
    dTilde g (y + blockInj i t) ≤
      dTilde g y + ((⟪-x, t⟫ + 1 / 2 * ‖t‖ ^ 2 : ℝ) : EReal) := by sorry

end DualRCD
