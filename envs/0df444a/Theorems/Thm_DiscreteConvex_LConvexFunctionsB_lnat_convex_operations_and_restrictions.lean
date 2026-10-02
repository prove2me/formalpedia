-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsB_lnat_convex_operations_and_restrictions
-- name    : DiscreteConvex.LConvexFunctionsB.lnat_convex_operations_and_restrictions
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:25:29.048985+00:00
-- url     : https://prove2.me/theorems/f10024ab-a792-435a-ac69-3ce8f65c5e64
-- title:
--   Theorem 7.11 -- lnat_convex_operations_and_restrictions
-- statement:
--   **Theorem 7.11** (p.184). Let $g,g_1,g_2\in L^\natural[\mathbb Z\to\mathbb R]$ be L$^\natural$-convex functions. (1) Operations (1)-(6) of Theorem 7.10 are valid for L$^\natural$-convex functions. (2) The restriction $g_{[a,b]}$ to the integer interval $[a,b]$ is L$^\natural$-convex provided its domain is nonempty. (3) The restriction $g_U$ to $U\subseteq V$ is L$^\natural$-convex provided its domain is nonempty.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.184, Theorem 7.11.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.184, Theorem 7.11

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LinearWeight
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ProjectionZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SeparablePerturbZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_IntervalRestrict
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_Restriction

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.11 (p.184). The six operations of Theorem 7.10 are valid for L♮-convex functions,
which additionally admit restriction to an integer interval and restriction to `U ⊆ V`. -/
theorem lnat_convex_operations_and_restrictions (g g1 g2 : (V → ℤ) → WithTop ℝ)
    (hg : LNaturalConvex g) (hg1 : LNaturalConvex g1) (hg2 : LNaturalConvex g2) :
    ((∀ lam : ℝ, 0 < lam → LNaturalConvex (fun p => PosScalarMul lam (g p))) ∧
     (∀ a : V → ℤ, ∀ beta : ℤ, beta ≠ 0 →
       LNaturalConvex (fun p => g (fun v => a v + beta * p v))) ∧
     (∀ x : V → ℝ, LNaturalConvex (LinearWeight g (fun v => - x v))) ∧
     (∀ U : Set V, (DomZ (ProjectionZ g U)).Nonempty → LNaturalConvex (ProjectionZ g U)) ∧
     (∀ psi : V → ℤ → WithTop ℝ, (DomZ (SeparablePerturbZ g psi)).Nonempty →
        LNaturalConvex (SeparablePerturbZ g psi)) ∧
     ((DomZ (fun p => g1 p + g2 p)).Nonempty → LNaturalConvex (fun p => g1 p + g2 p))) ∧
    (∀ a b : V → WithBot (WithTop ℤ), (DomZ (IntervalRestrict g a b)).Nonempty →
      LNaturalConvex (IntervalRestrict g a b)) ∧
    (∀ U : Finset V, (DomZ (Restriction g U)).Nonempty → LNaturalConvex (Restriction g U)) := by sorry

end DiscreteConvex.LConvexFunctionsB
