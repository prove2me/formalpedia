-- Prove2me | Theorems.Thm_BregmanPPA_Existence_theorem3
-- name    : BregmanPPA.Existence.theorem3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:38.329995+00:00
-- url     : https://prove2.me/theorems/c596a4e0-326b-40a8-b36c-36a38dd229c0
-- title:
--   Theorem 3 [5] (Brézis–Haraux) — int im(A + B) = int(im A + im B) and the same for closures
-- statement:
--   Let $H$ be a finite-dimensional real inner product space and let $A,B:H\to2^H$ be monotone operators such that
--
--   1. $\operatorname{dom}A\subseteq\operatorname{dom}B$;
--   2. $A+B$ is maximal monotone, where $(A+B)(x)=\{a+b: a\in Ax,\ b\in Bx\}$;
--   3. $B$ has the L-property.
--
--   Then
--   $$
--   \operatorname{int}\bigl(\operatorname{im}(A+B)\bigr)=\operatorname{int}(\operatorname{im}A+\operatorname{im}B)
--   \quad\text{and}\quad
--   \overline{\operatorname{im}(A+B)}=\overline{\operatorname{im}A+\operatorname{im}B},
--   $$
--   where $\operatorname{im}A+\operatorname{im}B$ is the Minkowski sum of the two images.
--
--   The inclusion $\operatorname{im}(A+B)\subseteq\operatorname{im}A+\operatorname{im}B$ is trivial; the theorem says the range of a sum is "almost" the sum of the ranges. The paper uses it with $A=T$ and $B=\nabla h$ to show that $(\nabla h+c_kT)^{-1}\circ\nabla h$ is defined on all of the zone of $h$.
--
--   **Formalization Note** "$A+B$ is maximal" is read as maximal monotone (published `IsMaximalMonotone`); the sum is the published `DouglasRachfordPPA.GenDR.opAdd`, with domain $\operatorname{dom}A\cap\operatorname{dom}B$, and images are `imOp`. The paper's conclusion (B) prints an overbar over each whole side, i.e. topological closures. Monotonicity of $B$ is stated as its own hypothesis as on the page, although the L-property as encoded already includes it.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 209, Theorem 3 (citing Brézis–Haraux [5])

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_BregmanPPA_Existence_LProperty

open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open scoped Pointwise

namespace BregmanPPA.Existence

/-- Theorem 3 [5] (Brézis–Haraux, p. 209): if `A`, `B` are monotone, `dom A ⊆ dom B`, `A + B` is
maximal monotone and `B` has the L-property, then `int im(A + B) = int(im A + im B)` and
`cl im(A + B) = cl(im A + im B)`. -/
theorem theorem3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (A B : H → Set H)
    (hA : IsMonotoneOp A) (hB : IsMonotoneOp B)
    (ha : dom A ⊆ dom B)
    (hb : IsMaximalMonotone (opAdd A B))
    (hc : HasLProperty B) :
    interior (imOp (opAdd A B)) = interior (imOp A + imOp B) ∧
    closure (imOp (opAdd A B)) = closure (imOp A + imOp B) := by sorry

end BregmanPPA.Existence
