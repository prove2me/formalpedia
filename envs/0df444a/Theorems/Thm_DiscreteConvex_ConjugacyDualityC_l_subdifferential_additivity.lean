-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityC_l_subdifferential_additivity
-- name    : DiscreteConvex.ConjugacyDualityC.l_subdifferential_additivity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:46:56.702603+00:00
-- url     : https://prove2.me/theorems/9ea15374-4830-4b15-b942-d72127bc6931
-- title:
--   Theorem 8.45 -- l_subdifferential_additivity
-- statement:
--   **Theorem 8.45** (p.233). The L-side mirror of Theorem 8.35: (1)-(2) subdifferentials of an infimal convolution of two L$^\natural$-convex functions intersect additively and nonemptily (real and integer versions); (3) the subdifferential of an L$^\natural_2$-(resp. L2-)convex function is M$^\natural_2$-(resp. M2-)convex.
--
--   **Formalization Note.** "$g_1\square g_2 > -\infty$" is omitted as a hypothesis: `WithTop ℝ` has no $-\infty$ element, so it is automatically satisfied by every value this codomain can represent.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.233, Theorem 8.45.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.233, Theorem 8.45

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_M2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_MNat2ConvexSet
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConv
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_InfConvE
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_L2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LNat2Convex
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SubDifferentialR
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_SubDifferentialZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegerValuedFn

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.45 (p.233). The L-side mirror of Theorem 8.35: subdifferentials of an infimal
convolution of two L♮-convex functions intersect additively, and the subdifferential of an
L♮₂-(resp. L2-)convex function is M♮₂-(resp. M2-)convex. The book's `g1 □ g2 > -∞` is carried as
`InfConvE g1 g2 p ≠ ⊥`; without it `InfConv` reads the junk value `0` (take `g1(p) = p₁` and
`g2(p) = -p₁ + p₂`, both L-convex, whose convolution is `-∞` everywhere) and the attainment
hypothesis is satisfied by that junk while the two subdifferentials are disjoint. -/
theorem l_subdifferential_additivity :
    (∀ g1 g2 : (V → ℤ) → WithTop ℝ, LNaturalConvex g1 → LNaturalConvex g2 →
      (∀ p : V → ℤ, InfConvE g1 g2 p ≠ ⊥) →
      (∀ p : V → ℤ, InfConv g1 g2 p ≠ ⊤ →
        ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ InfConv g1 g2 p = g1 p1 + g2 p2) →
      ∀ p ∈ DomZ (InfConv g1 g2), ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ p1 ∈ DomZ g1 ∧ p2 ∈ DomZ g2 ∧
        SubDifferentialR (InfConv g1 g2) p = SubDifferentialR g1 p1 ∩ SubDifferentialR g2 p2 ∧
          (SubDifferentialR g1 p1 ∩ SubDifferentialR g2 p2).Nonempty) ∧
    (∀ g1 g2 : (V → ℤ) → WithTop ℝ, LNaturalConvex g1 → LNaturalConvex g2 →
      IsIntegerValuedFn g1 → IsIntegerValuedFn g2 →
      (∀ p : V → ℤ, InfConvE g1 g2 p ≠ ⊥) →
      (∀ p : V → ℤ, InfConv g1 g2 p ≠ ⊤ →
        ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ InfConv g1 g2 p = g1 p1 + g2 p2) →
      ∀ p ∈ DomZ (InfConv g1 g2), ∃ p1 p2 : V → ℤ, p = p1 + p2 ∧ p1 ∈ DomZ g1 ∧ p2 ∈ DomZ g2 ∧
        SubDifferentialZ (InfConv g1 g2) p = SubDifferentialZ g1 p1 ∩ SubDifferentialZ g2 p2 ∧
          (SubDifferentialZ g1 p1 ∩ SubDifferentialZ g2 p2).Nonempty) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, LNat2Convex g → IsIntegerValuedFn g → ∀ p ∈ DomZ g,
      MNat2ConvexSet (SubDifferentialZ g p)) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, L2Convex g → IsIntegerValuedFn g → ∀ p ∈ DomZ g,
      M2ConvexSet (SubDifferentialZ g p)) := by sorry

end DiscreteConvex.ConjugacyDualityC
