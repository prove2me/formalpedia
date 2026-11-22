-- Prove2me | Theorems.Thm_CubicSurface27_residual_two_lines
-- name    : CubicSurface27.residual_two_lines
-- status  : Proved
-- author  : @jdenwood
-- created : 2026-11-22T10:08:49.266832+00:00
-- url     : https://prove2.me/theorems/5439b6fd-37d9-4704-b544-317ca6107d55
-- title:
--   A plane through two lines of a smooth cubic surface meets it in exactly three lines
-- statement:
--   Let $F$ be a homogeneous cubic form on $\mathbb{C}^4$ with $X=V(F)\subset\mathbb{P}^3$ smooth. Let $L$ be a line on $X$ (a $2$-dimensional subspace on which $F$ vanishes) and let $P\supseteq L$ be a $3$-dimensional subspace (a plane in $\mathbb{P}^3$) containing a second line $M\neq L$ of $X$. Then $P\cap X$ is the union of $L$ and two further lines $b,c$ of $X$, with $L,b,c$ pairwise distinct: every $x\in P$ with $F(x)=0$ lies in $L\cup b\cup c$.
-- source:
--   M. Reid, Undergraduate Algebraic Geometry, §7 (cubic surfaces and the 27 lines): by smoothness, the residual conic of a plane section through a line is a pair of distinct lines.

import Mathlib
import Definitions.Def_cubic_surface_27_layer

namespace CubicSurface27

theorem residual_two_lines (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (L : Submodule ℂ (Fin 4 → ℂ)) (hL : L ∈ linesOf F)
    (P : Submodule ℂ (Fin 4 → ℂ)) (hP : Module.finrank ℂ P = 3) (hLP : L ≤ P)
    (hM : ∃ M ∈ linesOf F, M ≤ P ∧ M ≠ L) :
    ∃ b ∈ linesOf F, ∃ c ∈ linesOf F, L ≠ b ∧ L ≠ c ∧ b ≠ c ∧ b ≤ P ∧ c ≤ P ∧
      ∀ x ∈ P, MvPolynomial.eval x F = 0 → x ∈ L ∨ x ∈ b ∨ x ∈ c := by sorry

end CubicSurface27
