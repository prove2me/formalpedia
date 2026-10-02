-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_l_separation_theorem
-- name    : DiscreteConvex.ConjugacyDualityB.l_separation_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:33:37.447981+00:00
-- url     : https://prove2.me/theorems/79cf03ea-ecbd-420a-bab2-52076bfba841
-- title:
--   Theorem 8.16 -- l_separation_theorem
-- statement:
--   **Theorem 8.16** (L-separation theorem; p.218). The L-side mirror of Theorem 8.15: an L$^\natural$-convex/concave pair satisfying $g\ge k$ is separated by an affine function, integral when $g,k$ are integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.218, Theorem 8.16.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.218, Theorem 8.16

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConcaveConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomERealConcave

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.16 (L-separation theorem; p.218). The L-side mirror of Theorem 8.15. -/
theorem l_separation_theorem (g k2 : (V → ℤ) → WithTop ℝ) (hg : LNaturalConvex g)
    (hk2 : LNaturalConvex k2)
    (hdom : (DomZ g ∩ DomZ k2).Nonempty ∨
      (DomEReal (ConvexConjugateZR g) ∩ DomERealConcave (ConcaveConjugateZR k2)).Nonempty)
    (hge : ∀ p : V → ℤ, g p + k2 p ≥ 0) :
    (∃ beta : ℝ, ∃ x : V → ℝ,
      (∀ p : V → ℤ, g p ≥ ((beta + ∑ v, x v * (p v : ℝ) : ℝ) : WithTop ℝ)) ∧
      (∀ p : V → ℤ, ((beta + ∑ v, x v * (p v : ℝ) : ℝ) : WithTop ℝ) + k2 p ≥ 0)) ∧
    (IsIntegerValuedFn g → IsIntegerValuedFn k2 →
      ∃ beta : ℤ, ∃ x : V → ℤ,
        (∀ p : V → ℤ, g p ≥ ((beta + ∑ v, (x v : ℝ) * (p v : ℝ) : ℝ) : WithTop ℝ)) ∧
        (∀ p : V → ℤ, ((beta + ∑ v, (x v : ℝ) * (p v : ℝ) : ℝ) : WithTop ℝ) + k2 p ≥ 0)) := by sorry

end DiscreteConvex.ConjugacyDualityB
