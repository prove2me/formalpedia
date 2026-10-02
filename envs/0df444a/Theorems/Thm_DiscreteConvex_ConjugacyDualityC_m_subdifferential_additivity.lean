-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_m_subdifferential_additivity
-- name    : DiscreteConvex.ConjugacyDualityC.m_subdifferential_additivity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:46:37.908958+00:00
-- url     : https://prove2.me/theorems/10345ac2-8c47-4304-853b-08eb1cda94ba
-- title:
--   Theorem 8.35 -- m_subdifferential_additivity
-- statement:
--   **Theorem 8.35** (p.228-229). (1) For M$^\natural$-convex $f_1,f_2$, $\partial_{\mathbb R}(f_1+f_2)(x)=\partial_{\mathbb R} f_1(x)+\partial_{\mathbb R} f_2(x)\ne\emptyset$. (2) The integer-valued analogue for $\partial_{\mathbb Z}$. (3) For M$^\natural_2$-(resp. M2-)convex $f$, $\partial_{\mathbb Z} f(x)$ is L$^\natural_2$-(resp. L2-)convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.228-229, Theorem 8.35.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.228-229, Theorem 8.35

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_M2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SubDifferentialR
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SubDifferentialZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegerValuedFn

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.35 (p.228-229). Subdifferentials add under the sum of two M♮-convex functions, and
the subdifferential of an M♮₂-(resp. M2-)convex function is L♮₂-(resp. L2-)convex. -/
theorem m_subdifferential_additivity :
    (∀ f1 f2 : (V → ℤ) → WithTop ℝ, MNaturalConvex f1 → MNaturalConvex f2 →
      ∀ x ∈ DomZ f1 ∩ DomZ f2,
      SubDifferentialR (fun y => f1 y + f2 y) x = SubDifferentialR f1 x + SubDifferentialR f2 x ∧
        (SubDifferentialR (fun y => f1 y + f2 y) x).Nonempty) ∧
    (∀ f1 f2 : (V → ℤ) → WithTop ℝ, MNaturalConvex f1 → MNaturalConvex f2 →
      IsIntegerValuedFn f1 → IsIntegerValuedFn f2 → ∀ x ∈ DomZ f1 ∩ DomZ f2,
      SubDifferentialZ (fun y => f1 y + f2 y) x = SubDifferentialZ f1 x + SubDifferentialZ f2 x ∧
        (SubDifferentialZ (fun y => f1 y + f2 y) x).Nonempty) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNat2Convex f → IsIntegerValuedFn f → ∀ x ∈ DomZ f,
      LNat2ConvexSet (SubDifferentialZ f x)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, M2Convex f → IsIntegerValuedFn f → ∀ x ∈ DomZ f,
      L2ConvexSet (SubDifferentialZ f x)) := by sorry

end DiscreteConvex.ConjugacyDualityC
