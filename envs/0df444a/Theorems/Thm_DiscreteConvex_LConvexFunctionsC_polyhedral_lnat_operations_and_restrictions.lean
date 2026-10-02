-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_polyhedral_lnat_operations_and_restrictions
-- name    : DiscreteConvex.LConvexFunctionsC.polyhedral_lnat_operations_and_restrictions
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:40:24.338035+00:00
-- url     : https://prove2.me/theorems/cfb0003c-f443-47b7-96ff-89e617ad979c
-- title:
--   Theorem 7.32 -- polyhedral_lnat_operations_and_restrictions
-- statement:
--   **Theorem 7.32** (p.193). Let $g,g_1,g_2\in L^\natural[\mathbb R\to\mathbb R]$ be polyhedral L$^\natural$-convex functions. (1) Operations (1)-(6) of Theorem 7.31 are valid for polyhedral L$^\natural$-convex functions. (2) The restriction $g_{[a,b]}$ to the real interval $[a,b]$ is polyhedral L$^\natural$-convex provided its domain is nonempty. (3) The restriction $g_U$ to $U\subseteq V$ is polyhedral L$^\natural$-convex provided its domain is nonempty.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.193, Theorem 7.32.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.193, Theorem 7.32

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvexR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LinearWeightR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ProjectionR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SeparablePerturbInfConvR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IntervalRestrictR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_RestrictionR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.32 (p.193). The six operations of Theorem 7.31 are valid for polyhedral L♮-convex
functions, which additionally admit restriction to a real interval and restriction to `U ⊆ V`. -/
theorem polyhedral_lnat_operations_and_restrictions (g g1 g2 : (V → ℝ) → WithTop ℝ)
    (hg : LNaturalConvexR g) (hg1 : LNaturalConvexR g1) (hg2 : LNaturalConvexR g2) :
    ((∀ lam : ℝ, 0 < lam → LNaturalConvexR (fun p => PosScalarMul lam (g p))) ∧
     (∀ a : V → ℝ, ∀ beta : ℝ, beta ≠ 0 →
       LNaturalConvexR (fun p => g (fun v => a v + beta * p v))) ∧
     (∀ x : V → ℝ, LNaturalConvexR (LinearWeightR g (fun v => - x v))) ∧
     (∀ U : Set V, (DomR (ProjectionR g U)).Nonempty → LNaturalConvexR (ProjectionR g U)) ∧
     (∀ psi : V → ℝ → WithTop ℝ, (DomR (SeparablePerturbInfConvR g psi)).Nonempty →
        LNaturalConvexR (SeparablePerturbInfConvR g psi)) ∧
     ((DomR (fun p => g1 p + g2 p)).Nonempty → LNaturalConvexR (fun p => g1 p + g2 p))) ∧
    (∀ a b : V → WithBot (WithTop ℝ), (DomR (IntervalRestrictR g a b)).Nonempty →
      LNaturalConvexR (IntervalRestrictR g a b)) ∧
    (∀ U : Finset V, (DomR (RestrictionR g U)).Nonempty → LNaturalConvexR (RestrictionR g U)) := by sorry

end DiscreteConvex.LConvexFunctionsC
