-- Prove2me | Theorems.Thm_CubicSurface27_cauchy_schwarz_bound
-- name    : CubicSurface27.cauchy_schwarz_bound
-- status  : Proved
-- author  : @LG
-- created : 2026-11-20T13:51:42.824789+00:00
-- url     : https://prove2.me/theorems/9c760a38-f752-40dc-b4ab-d41d1e344733
-- title:
--   Cauchy–Schwarz bound $a < 3$ for $(-1)$-classes
-- statement:
--   The exhaustiveness step of the count. Let $D=aL-\sum_{i=1}^6 b_iE_i$ be the class of an irreducible rational curve other than the exceptional divisors, so $a>0$ and $b_i\ge0$ are integers. Self-intersection $-1$ gives $a^2-\sum_i b_i^2=-1$; the adjunction formula with $K_X=-3L+\sum_iE_i$ gives $3a-\sum_i b_i=1$.
--
--   Cauchy–Schwarz applied to $(1,\dots,1)$ and $(b_1,\dots,b_6)$ yields $(\sum_i b_i)^2\le 6\sum_i b_i^2$. Substituting $\sum_i b_i=3a-1$ and $\sum_i b_i^2=a^2+1$ gives
--   $$(3a-1)^2\le 6(a^2+1),\qquad\text{i.e.}\qquad 3a^2-6a-5\le0,$$
--   whence $a<3$. This item states the final bound $a<3$ under the two numerical conditions.
--
--   **Formalization Note.** Pure integer arithmetic; the geometric origin of the two hypotheses (self-intersection and adjunction) is recorded in the source and is not assumed here.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part I, 'Counting lines', the exhaustiveness paragraph: D = aL − ΣbᵢEᵢ with a > 0, bᵢ ≥ 0, the equalities a² − Σbᵢ² = −1 and 3a − Σbᵢ = 1, Cauchy–Schwarz, and the conclusion a < 3.

import Mathlib
open Finset

namespace CubicSurface27

theorem cauchy_schwarz_bound (a : ℤ) (b : Fin 6 → ℤ)
    (ha : 0 < a) (hb : ∀ i, 0 ≤ b i)
    (hself : a ^ 2 - ∑ i : Fin 6, (b i) ^ 2 = -1)
    (hadj : 3 * a - ∑ i : Fin 6, b i = 1) :
    a < 3 := by sorry

end CubicSurface27
