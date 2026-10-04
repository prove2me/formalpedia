-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_entropicBarrier_isBarrier
-- name    : EntropicBarrier.Universal.entropicBarrier_isBarrier
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:04:24.794579+00:00
-- url     : https://prove2.me/theorems/5ef4b0a8-9571-44b9-a554-67969b77440d
-- title:
--   §4, p. 6 — the entropic barrier $f^*$ is a barrier for $\mathcal K$
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body with entropic barrier $f^*$. Then $f^*$ is a barrier for $\mathcal K$:
--   $$f^*(x)\longrightarrow+\infty\qquad(x\to\partial\mathcal K,\ x\in\operatorname{int}(\mathcal K)).$$
--
--   This is the first of the three properties in Theorem 1; the paper derives it from $\nabla f(\mathbb R^n)=\operatorname{int}(\mathcal K)$.
--
--   **Formalization Note** For every point $x_0$ of the topological frontier of $\mathcal K$, $f^*$ tends to $+\infty$ along the neighbourhood filter of $x_0$ restricted to $\operatorname{int}(\mathcal K)$.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 6, §4, first sentence

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem entropicBarrier_isBarrier {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    IsBarrier K (entropicBarrier K) := by sorry

end EntropicBarrier.Universal
