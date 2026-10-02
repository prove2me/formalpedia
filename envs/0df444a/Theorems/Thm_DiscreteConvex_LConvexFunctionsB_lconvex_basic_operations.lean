-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_lconvex_basic_operations
-- name    : DiscreteConvex.LConvexFunctionsB.lconvex_basic_operations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:22:25.406606+00:00
-- url     : https://prove2.me/theorems/6040ceb5-0d01-450d-a8d4-d8c7f562ed54
-- title:
--   Theorem 7.10 -- lconvex_basic_operations
-- statement:
--   **Theorem 7.10** (p.183-184). Let $g,g_1,g_2\in L[\mathbb Z\to\mathbb R]$ be L-convex functions. (1) $\lambda g$ is L-convex for $\lambda\in\mathbb R_{++}$. (2) $g(a+\beta p)$ is L-convex in $p$, for $a\in\mathbb Z^V$, $\beta\in\mathbb Z\setminus\{0\}$. (3) $g[-x]$ is L-convex for $x\in\mathbb R^V$. (4) The projection $g_U$ is L-convex provided $g_U>-\infty$. (5) The infimal convolution of $g$ with a separable convex function is L-convex provided it is $>-\infty$. (6) The sum $g_1+g_2$ is L-convex provided its domain is nonempty.
--
--   **Formalization Note.** All six parts are stated in full (unlike several sibling missions' 4-of-8-part reductions for the M-convex analogue, Theorem 6.13 — this book's own six-part L-convex operations theorem needed no cut). "$>-\infty$" is replaced by the equivalent, already-established `(DomZ ...).Nonempty` hypothesis (`WithTop ℝ` has no $-\infty$ element), matching mission `24-ch06d-mconvexfunctions`'s identical substitution for `ProjectionR`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.183-184, Theorem 7.10.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.183-184, Theorem 7.10

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LinearWeight
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ProjectionZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SeparablePerturbZ

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.10 (p.183-184). Basic operations on L-convex functions: scaling, affine
reparametrization, linear perturbation, projection, infimal convolution with a separable
function, and sum. -/
theorem lconvex_basic_operations (g g1 g2 : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g) :
    (∀ lam : ℝ, 0 < lam →
      SBF (fun p => PosScalarMul lam (g p)) ∧ TRF (fun p => PosScalarMul lam (g p))) ∧
    (∀ a : V → ℤ, ∀ beta : ℤ, beta ≠ 0 →
      SBF (fun p => g (fun v => a v + beta * p v)) ∧
      TRF (fun p => g (fun v => a v + beta * p v))) ∧
    (∀ x : V → ℝ, SBF (LinearWeight g (fun v => - x v)) ∧ TRF (LinearWeight g (fun v => - x v))) ∧
    (∀ U : Set V, (DomZ (ProjectionZ g U)).Nonempty →
      SBF (ProjectionZ g U) ∧ TRF (ProjectionZ g U)) ∧
    (∀ psi : V → ℤ → WithTop ℝ, (DomZ (SeparablePerturbZ g psi)).Nonempty →
      SBF (SeparablePerturbZ g psi) ∧ TRF (SeparablePerturbZ g psi)) ∧
    ((DomZ (fun p => g1 p + g2 p)).Nonempty → SBF g1 → TRF g1 → SBF g2 → TRF g2 →
      SBF (fun p => g1 p + g2 p) ∧ TRF (fun p => g1 p + g2 p)) := by sorry

end DiscreteConvex.LConvexFunctionsB
