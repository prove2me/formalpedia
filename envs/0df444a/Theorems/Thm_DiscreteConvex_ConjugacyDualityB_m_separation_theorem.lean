-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityB_m_separation_theorem
-- name    : DiscreteConvex.ConjugacyDualityB.m_separation_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T01:35:37.12599+00:00
-- url     : https://prove2.me/theorems/b4c32260-0dfe-4b4b-85c3-ba2a7e86ed39
-- title:
--   Theorem 8.15 -- m_separation_theorem
-- statement:
--   **Theorem 8.15** (M-separation theorem; p.217). Let $f$ be M$^\natural$-convex and $h$ M$^\natural$-concave with $\operatorname{dom}_{\mathbb Z} f\cap\operatorname{dom}_{\mathbb Z} h\ne\emptyset$ or $\operatorname{dom}_{\mathbb R} f^\bullet\cap\operatorname{dom}_{\mathbb R} h^\circ\ne\emptyset$. If $f\ge h$ on $\mathbb Z^V$, there exist $\alpha^*\in\mathbb R$, $p^*\in\mathbb R^V$ separating $f$ and $h$ by an affine function; if $f,h$ are integer valued, the separator is integral.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.217, Theorem 8.15.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.217, Theorem 8.15

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNaturalConvex
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConcaveConjugateZR
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomERealConcave

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 8.15 (M-separation theorem; p.217). A pointwise inequality `f ≥ h` between an
M♮-convex and an M♮-concave function is witnessed by an affine separator; the witness is integral
when `f, h` are integer valued. -/
theorem m_separation_theorem (f h2 : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f)
    (hh2 : MNaturalConvex h2)
    (hdom : (DomZ f ∩ DomZ h2).Nonempty ∨
      (DomEReal (ConvexConjugateZR f) ∩ DomERealConcave (ConcaveConjugateZR h2)).Nonempty)
    (hge : ∀ x : V → ℤ, f x + h2 x ≥ 0) :
    (∃ alpha : ℝ, ∃ p : V → ℝ,
      (∀ x : V → ℤ, f x ≥ ((alpha + ∑ v, p v * (x v : ℝ) : ℝ) : WithTop ℝ)) ∧
      (∀ x : V → ℤ, ((alpha + ∑ v, p v * (x v : ℝ) : ℝ) : WithTop ℝ) + h2 x ≥ 0)) ∧
    (IsIntegerValuedFn f → IsIntegerValuedFn h2 →
      ∃ alpha : ℤ, ∃ p : V → ℤ,
        (∀ x : V → ℤ, f x ≥ ((alpha + ∑ v, (p v : ℝ) * (x v : ℝ) : ℝ) : WithTop ℝ)) ∧
        (∀ x : V → ℤ, ((alpha + ∑ v, (p v : ℝ) * (x v : ℝ) : ℝ) : WithTop ℝ) + h2 x ≥ 0)) := by sorry

end DiscreteConvex.ConjugacyDualityB
