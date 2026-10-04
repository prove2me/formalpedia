-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_entropicBarrier_selfConcordant
-- name    : EntropicBarrier.Universal.entropicBarrier_selfConcordant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:04:38.263277+00:00
-- url     : https://prove2.me/theorems/942c191b-0f69-4e33-af76-d7851e786ae5
-- title:
--   §4, pp. 6–7 — the entropic barrier $f^*$ is self-concordant on $\operatorname{int}(\mathcal K)$
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body with entropic barrier $f^*$. Then $f^*$ is $C^3$-smooth and convex on $\operatorname{int}(\mathcal K)$ and satisfies, for all $x\in\operatorname{int}(\mathcal K)$ and $h\in\mathbb R^n$,
--   $$\nabla^3 f^*(x)[h,h,h]\le 2\left(\nabla^2 f^*(x)[h,h]\right)^{3/2}.$$
--
--   This is the second of the three properties in Theorem 1.
--
--   **Formalization Note** Stated with the published `ConvexOptimization.IsSelfConcordantOn (interior K)`; see the definition item for its equivalence with (2).
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), pp. 6-7, §4

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem entropicBarrier_selfConcordant {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    ConvexOptimization.IsSelfConcordantOn (interior K) (entropicBarrier K) := by sorry

end EntropicBarrier.Universal
