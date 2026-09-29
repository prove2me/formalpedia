-- Prove2me | Theorems.Thm_BiconvexProg_BranchBound_grad_bound
-- name    : BiconvexProg.BranchBound.grad_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:58:12.432989+00:00
-- url     : https://prove2.me/theorems/defcf892-7482-4ba8-aaf1-b366f2bc189a
-- title:
--   Gradient bound — $\gamma_i = \|(\beta_i,\alpha_i)\|$ at a corner, and $\max\{\|\nabla h_{i1}\|, \|\nabla h_{i2}\|\} \le \gamma_i$ on sub-rectangles
-- statement:
--   Let $\Omega_i = [l, L] \times [m, M] \subseteq \mathbb{R}^2$ with $l \le L$ and $m \le M$, and let
--
--   $$\gamma_i = \max\{\|\nabla x_i y_i\| : (x_i, y_i) \in \Omega_i\}$$
--
--   (Euclidean norm, $\nabla(x_i y_i) = (y_i, x_i)$). Then:
--
--   1. $\gamma_i = \|(\beta_i, \alpha_i)\|$ for some corner $(\alpha_i, \beta_i) \in \{l, L\} \times \{m, M\}$ of $\Omega_i$;
--   2. for every sub-rectangle $[l', L'] \times [m', M'] \subseteq \Omega_i$, the affine functions $h_{i1} = m' x_i + l' y_i - l' m'$ and $h_{i2} = M' x_i + L' y_i - L' M'$ have gradients $(m', l')$ and $(M', L')$ satisfying
--
--   $$\max\{\|\nabla h_{i1}\|,\ \|\nabla h_{i2}\|\} \le \gamma_i .$$
--
--   Since the refining rule only shrinks rectangles, the pieces of every node function of the algorithm have gradients bounded by $\gamma_i$, uniformly over all nodes and stages. This is the Lipschitz constant behind the equicontinuity estimate.
--
--   **Formalization Note** The gradient norms are written out as $\sqrt{m'^2 + l'^2}$ and $\sqrt{M'^2 + L'^2}$. The paper's "for every $j$ and all $k$" is stated for every sub-rectangle, which contains all rectangles produced by the refining rule.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 281, Convergence proof (maximum norm problem, corner remark, bound on ‖∇h_{i1}^{kj}‖, ‖∇h_{i2}^{kj}‖)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_gradNormMax

namespace BiconvexProg.BranchBound

/-- Gradient bound (p. 281). Let `γ = max {‖∇(xy)‖ : (x, y) ∈ [l, L] × [m, M]}` (Euclidean norm,
`∇(xy) = (y, x)`). Then `γ = ‖(β, α)‖` for a corner `(α, β)` of the rectangle, and for every
sub-rectangle `[l', L'] × [m', M']` the gradients `(m', l')` of `h₁ = m'x + l'y − l'm'` and
`(M', L')` of `h₂ = M'x + L'y − L'M'` have Euclidean norm at most `γ`. -/
theorem grad_bound (l L m M : ℝ) (hlL : l ≤ L) (hmM : m ≤ M) :
    (∃ α ∈ ({l, L} : Set ℝ), ∃ β ∈ ({m, M} : Set ℝ),
      gradNormMax l L m M = Real.sqrt (β ^ 2 + α ^ 2)) ∧
    ∀ l' L' m' M' : ℝ, l ≤ l' → l' ≤ L' → L' ≤ L → m ≤ m' → m' ≤ M' → M' ≤ M →
      Real.sqrt (m' ^ 2 + l' ^ 2) ≤ gradNormMax l L m M ∧
        Real.sqrt (M' ^ 2 + L' ^ 2) ≤ gradNormMax l L m M := by sorry

end BiconvexProg.BranchBound
