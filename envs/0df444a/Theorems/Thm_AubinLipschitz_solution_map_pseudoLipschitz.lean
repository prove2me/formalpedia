-- Prove2me | Theorems.Thm_AubinLipschitz_solution_map_pseudoLipschitz
-- name    : AubinLipschitz.solution_map_pseudoLipschitz
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:54:37.237527+00:00
-- url     : https://prove2.me/theorems/23a37a02-cf0b-4e12-9d22-5eef01c1d35f
-- title:
--   §5, Theorem 1 — solutions and multipliers are pseudo-Lipschitz in $(p,y,A)$, with the formula for their derivative
-- statement:
--   Let $X,Y$ be finite-dimensional, $A_0:X\to Y$ linear, and $U:X\to\mathbb R\cup\{+\infty\}$, $V:Y\to\mathbb R\cup\{+\infty\}$ proper, lower semicontinuous and convex. Let
--
--   $$
--   y_0\in\operatorname{Int}(\operatorname{Dom}V-A_0\operatorname{Dom}U),\qquad
--   p_0\in\operatorname{Int}(A_0^*\operatorname{Dom}V^*+\operatorname{Dom}U^*),
--   $$
--
--   and let $(x_0,q_0)\in X\times Y^*$ be a solution of problem (3). Let $M$ be the process from $X\times Y^*$ to $X^*\times Y$ given by
--
--   $$
--   M=\begin{pmatrix}\partial^2U(x_0,p_0-A_0^*q_0) & A_0^*\\[2pt] -A_0 & \big(\partial^2V(A_0x_0+y_0,q_0)\big)^{-1}\end{pmatrix},
--   $$
--
--   and assume that $M$ is surjective. Let $F^{-1}(p,y,A)$ be the set of solutions $(x,q)$ of $p\in\partial U(x)+A^*q$, $y\in-Ax+\partial V^*(q)$. Then
--
--   1. $F^{-1}$ is pseudo-Lipschitz around $(p_0,y_0,A_0,x_0,q_0)$;
--   2. for all $\delta p,\delta y,\delta A,\delta x,\delta q$,
--
--   $$
--   (\delta x,\delta q)\in CF^{-1}(p_0,y_0,A_0;x_0,q_0)(\delta p,\delta y,\delta A)
--   \iff
--   \begin{pmatrix}\delta x\\\delta q\end{pmatrix}\in M^{-1}\begin{pmatrix}\delta p-\delta A^*\cdot q_0\\ \delta y+\delta A\cdot x_0\end{pmatrix}.
--   $$
--
--   So near a regular solution, solutions and Lagrange multipliers move in a Lipschitz manner with the data of the problem, including the constraint operator, and their sensitivity is given by the inverse of the matrix of generalized second derivatives.
--
--   **Formalization Note** The parameter and solution spaces carry Lean's sup norm of the product; the pseudo-Lipschitz property and the Clarke cone do not change under an equivalent norm.
--
--   Differences from the source:
--   - encoding: "process from X × Y to itself" → a process from X × Y* to X* × Y; reason: the printed phrase identifies each space with its dual, and the entries of the matrix have these domains and ranges.
--   - encoding: "Ax₀" in the matrix (twice, p.32) → A₀x₀; reason: a misprint, since (11)–(12), p.33, and Corollary 1, p.35, have A₀x₀ and the second derivative is taken at the base point.
--   - encoding: "monotone closed convex process … is surjective" → only surjectivity is a hypothesis; reason: "monotone closed convex" are properties of this matrix, not assumptions (§2, p.19).
--   - encoding: a linear operator A₀ from X to Y → a continuous linear map; reason: every linear map between finite-dimensional normed spaces is continuous.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, Theorem 1, (6)–(8), p.32, under (1)–(2), p.31

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_AubinLipschitz_IsPrimalDualSolution
import Definitions.Def_AubinLipschitz_IsSurjectiveProcess
import Definitions.Def_AubinLipschitz_matrixProcess
import Definitions.Def_AubinLipschitz_PseudoLipschitzAround
import Definitions.Def_AubinLipschitz_solMap
open RockafellarMaxMono.Shared

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, Theorem 1, p.32: under the assumptions (1), (2), let `(x₀, q₀)` be a solution of
problem (3), and assume that the process
`[[∂²U(x₀, p₀ − A₀*q₀), A₀*], [−A₀, (∂²V(A₀x₀ + y₀, q₀))⁻¹]]` is surjective. Then
(6) `F⁻¹` is pseudo-Lipschitz around `(p₀, y₀, A₀, x₀, q₀)`, and
(7)–(8) `(δx, δq) ∈ CF⁻¹(p₀, y₀, A₀; x₀, q₀)(δp, δy, δA)` if and only if
`(δp − δA*·q₀, δy + δA·x₀)` belongs to the image of `(δx, δq)` under that process.

**Formalization Note** `X*` is `StrongDual ℝ X`, `A*q` is `q.comp A`, `ℝ ∪ {+∞}` is `EReal`
with the value `⊥` excluded by `ProperConvex`, and `∂V*(q)` is taken in `Y` (`subdiffConj`). The
parameter space `X* × Y × L(X, Y)` and the solution space `X × Y*` carry Lean's sup norm of the
operator norms; all the notions involved are unchanged by equivalent norms. -/
theorem solution_map_pseudoLipschitz {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (U : X → EReal) (V : Y → EReal) (hU : ProperConvex U) (hUlsc : LowerSemicontinuous U)
    (hV : ProperConvex V) (hVlsc : LowerSemicontinuous V) (A₀ : X →L[ℝ] Y)
    (p₀ : StrongDual ℝ X) (y₀ : Y)
    (hy₀ : y₀ ∈ interior {z : Y | ∃ v ∈ effDom V, ∃ u ∈ effDom U, z = v - A₀ u})
    (hp₀ : p₀ ∈ interior {r : StrongDual ℝ X | ∃ q ∈ effDom (conj V), ∃ s ∈ effDom (conj U),
      r = q.comp A₀ + s})
    (x₀ : X) (q₀ : StrongDual ℝ Y) (hsol : IsPrimalDualSolution U V A₀ p₀ y₀ x₀ q₀)
    (hsurj : IsSurjectiveProcess (matrixProcess U V A₀ p₀ y₀ x₀ q₀)) :
    PseudoLipschitzAround (solMap U V) (p₀, y₀, A₀) (x₀, q₀) ∧
    ∀ (δp : StrongDual ℝ X) (δy : Y) (δA : X →L[ℝ] Y) (δx : X) (δq : StrongDual ℝ Y),
      (δx, δq) ∈ clarkeDeriv (solMap U V) (p₀, y₀, A₀) (x₀, q₀) (δp, δy, δA) ↔
        (δp - q₀.comp δA, δy + δA x₀) ∈ matrixProcess U V A₀ p₀ y₀ x₀ q₀ (δx, δq) := by sorry

end AubinLipschitz
