-- Prove2me | Theorems.Thm_DiscreteConvex_IntegralConvexityB_theorem_3_6_fenchel_duality
-- name    : DiscreteConvex.IntegralConvexityB.theorem_3_6_fenchel_duality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:06:01.125926+00:00
-- url     : https://prove2.me/theorems/2d183cfd-83fb-4302-af66-53d14d039e6a
-- title:
--   Theorem 3.6 -- Fenchel duality (GOAL)
-- statement:
--   $\inf\{f-h\}=\sup\{h^\circ-f^\bullet\}$ under one of four alternative hypotheses, with attainment when the common value is finite.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.105, Theorem 3.6.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.105, Theorem 3.6

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConcave
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsClosedConvexF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsClosedConcaveF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE
import Definitions.Def_DiscreteConvex_IntegralConvexityB_RelInt
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConcave
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConjF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConcConjF

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.105, Theorem 3.6 — the goal of this mission —
in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- **Theorem 3.6** (Fenchel duality, goal). Let `f` be a proper convex function and `h` a
proper concave function, and assume at least one of (a1), (a2), (b1), (b2). Then
`inf{f(x)-h(x)} = sup{h◦(p)-f•(p)}`. Moreover, if this common value is finite, the supremum is
attained under (a1)/(a2) and the infimum is attained under (b1)/(b2). The infimum clause carries
(b1) or (b2) themselves, not merely closedness: `f(x) = e^x` and `h = 0` on `ℝ` are closed, the
infimum of `f - h` is `0` and it is not attained. -/
theorem theorem_3_6_fenchel_duality {V : Type*} [Fintype V] (f h : (V → ℝ) → EReal)
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (hyp : (RelInt (DomE f) ∩ RelInt (DomE h)).Nonempty ∨
      (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧ (DomE f ∩ DomE h).Nonempty) ∨
      (IsClosedConvexF f ∧ IsClosedConcaveF h ∧
        (RelInt (DomE (ConjF f)) ∩ RelInt (DomE (ConcConjF h))).Nonempty) ∨
      (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧
        (DomE (ConjF f) ∩ DomE (ConcConjF h)).Nonempty)) :
    (sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} =
        sSup {v : EReal | ∃ p : V → ℝ, v = ConcConjF h p - ConjF f p}) ∧
      (∀ delta : ℝ,
        sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} = (delta : EReal) →
          ((RelInt (DomE f) ∩ RelInt (DomE h)).Nonempty ∨
              (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧ (DomE f ∩ DomE h).Nonempty) →
            ∃ p ∈ DomE (ConjF f) ∩ DomE (ConcConjF h),
              ConcConjF h p - ConjF f p = (delta : EReal)) ∧
          ((IsClosedConvexF f ∧ IsClosedConcaveF h ∧
                (RelInt (DomE (ConjF f)) ∩ RelInt (DomE (ConcConjF h))).Nonempty) ∨
              (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧
                (DomE (ConjF f) ∩ DomE (ConcConjF h)).Nonempty) →
            ∃ x ∈ DomE f ∩ DomE h, f x - h x = (delta : EReal))) := by sorry

end DiscreteConvex.IntegralConvexityB
