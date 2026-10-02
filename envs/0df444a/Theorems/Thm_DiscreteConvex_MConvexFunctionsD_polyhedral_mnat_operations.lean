-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsD_polyhedral_mnat_operations
-- name    : DiscreteConvex.MConvexFunctionsD.polyhedral_mnat_operations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:55:47.033354+00:00
-- url     : https://prove2.me/theorems/7815a92a-60f9-4f99-b634-bd71d118738a
-- title:
--   Theorem 6.50 -- polyhedral_mnat_operations
-- statement:
--   **Theorem 6.50** (p.163). Let $f\in M^\natural[\mathbb R\to\mathbb R]$ be polyhedral M$^\natural$-convex. (1) Operations (1)-(4) of Theorem 6.49 are valid for polyhedral M$^\natural$-convex functions. (2) For $U\subseteq V$, the projection $f^U$ is polyhedral M$^\natural$-convex provided $f^U > -\infty$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Theorem 6.50.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Theorem 6.50

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvexR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_PosScalarMul
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_LinearWeightR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsConvexUniv
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_SeparablePerturbR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ProjectionR

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.50 (p.182), operations (1)-(4) plus the projection (2). -/
theorem polyhedral_mnat_operations (f : (V → ℝ) → WithTop ℝ) (hf : MNaturalConvexR f) :
    (∀ lam : ℝ, 0 < lam → MNaturalConvexR (fun x => PosScalarMul lam (f x))) ∧
    (∀ (a : V → ℝ) (beta : ℝ), beta ≠ 0 → MNaturalConvexR (fun x => f (fun v => a v + beta * x v))) ∧
    (∀ p : V → ℝ, MNaturalConvexR (LinearWeightR f p)) ∧
    (∀ phi : V → ℝ → WithTop ℝ, (∀ v, IsConvexUniv (phi v)) →
      (DomR (SeparablePerturbR f phi)).Nonempty → MNaturalConvexR (SeparablePerturbR f phi)) ∧
    (∀ U : Finset V, (DomR (ProjectionR f U)).Nonempty → MNaturalConvexR (ProjectionR f U)) := by sorry

end DiscreteConvex.MConvexFunctionsD
