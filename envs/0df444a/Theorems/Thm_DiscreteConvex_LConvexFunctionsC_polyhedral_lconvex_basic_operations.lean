-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_polyhedral_lconvex_basic_operations
-- name    : DiscreteConvex.LConvexFunctionsC.polyhedral_lconvex_basic_operations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:35:25.536341+00:00
-- url     : https://prove2.me/theorems/66571c8d-7687-42a8-9a82-40304b60182f
-- title:
--   Theorem 7.31 -- polyhedral_lconvex_basic_operations
-- statement:
--   **Theorem 7.31** (p.192-193). Let $g,g_1,g_2\in L[\mathbb R\to\mathbb R]$ be polyhedral L-convex functions. (1) $\lambda g$ is polyhedral L-convex for $\lambda\in\mathbb R_{++}$. (2) $g(a+\beta p)$ is polyhedral L-convex in $p$, for $a\in\mathbb R^V$, $\beta\in\mathbb R\setminus\{0\}$. (3) $g[-x]$ is polyhedral L-convex for $x\in\mathbb R^V$. (4) The projection $g_U$ is polyhedral L-convex provided $g_U>-\infty$. (5) The infimal convolution of $g$ with a separable convex function is polyhedral L-convex provided it is $>-\infty$. (6) The sum $g_1+g_2$ is polyhedral L-convex provided its domain is nonempty.
--
--   **Formalization Note.** All six parts are stated in full, the real-variable analogue of chunk `26-ch07b-lconvexfunctions`'s Theorem 7.10. "$>-\infty$" is replaced by the equivalent `(DomR ...).Nonempty` hypothesis (`WithTop ℝ` has no $-\infty$ element).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192-193, Theorem 7.31.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.192-193, Theorem 7.31

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ProjectionR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SeparablePerturbInfConvR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.31 (p.192-193). Basic operations on polyhedral L-convex functions. -/
theorem polyhedral_lconvex_basic_operations (g g1 g2 : (V → ℝ) → WithTop ℝ) (hg : SBFR g ∧ TRFR g) :
    (∀ lam : ℝ, 0 < lam →
      SBFR (fun p => PosScalarMul lam (g p)) ∧ TRFR (fun p => PosScalarMul lam (g p))) ∧
    (∀ a : V → ℝ, ∀ beta : ℝ, beta ≠ 0 →
      SBFR (fun p => g (fun v => a v + beta * p v)) ∧
      TRFR (fun p => g (fun v => a v + beta * p v))) ∧
    (∀ x : V → ℝ, SBFR (LinearWeightR g (fun v => - x v)) ∧ TRFR (LinearWeightR g (fun v => - x v))) ∧
    (∀ U : Set V, (DomR (ProjectionR g U)).Nonempty →
      SBFR (ProjectionR g U) ∧ TRFR (ProjectionR g U)) ∧
    (∀ psi : V → ℝ → WithTop ℝ, (DomR (SeparablePerturbInfConvR g psi)).Nonempty →
      SBFR (SeparablePerturbInfConvR g psi) ∧ TRFR (SeparablePerturbInfConvR g psi)) ∧
    ((DomR (fun p => g1 p + g2 p)).Nonempty → SBFR g1 → TRFR g1 → SBFR g2 → TRFR g2 →
      SBFR (fun p => g1 p + g2 p) ∧ TRFR (fun p => g1 p + g2 p)) := by sorry

end DiscreteConvex.LConvexFunctionsC
