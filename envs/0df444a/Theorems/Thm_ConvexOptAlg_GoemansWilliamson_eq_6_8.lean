-- Prove2me | Theorems.Thm_ConvexOptAlg_GoemansWilliamson_eq_6_8
-- name    : ConvexOptAlg.GoemansWilliamson.eq_6_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:22:29.589144+00:00
-- url     : https://prove2.me/theorems/8e1d1061-0dd1-40d5-b1ae-589031aadc0d
-- title:
--   Eq. (6.8), p. 346 — 1 − (2/π) arcsin(t) ≥ 0.878(1 − t) for all t ∈ [−1, 1]
-- statement:
--   For every real $t\in[-1,1]$,
--
--   $$1-\frac{2}{\pi}\arcsin(t)\ \ge\ 0.878\,(1-t).$$
--
--   This one-variable inequality is the source of the Goemans–Williamson constant: the best constant is $\min_{0<\theta\le\pi}\frac{2\theta}{\pi(1-\cos\theta)}\approx0.87856$, and $0.878$ lies below it. The book uses (6.8) without proof in the proof of Theorem 6.11.
-- source:
--   Bubeck, arXiv:1405.4980v2, Eq. (6.8), proof of Theorem 6.11, p. 346

import Mathlib
import Definitions.Def_ConvexOptAlg_GoemansWilliamson_Defs

namespace ConvexOptAlg.GoemansWilliamson

/-- Inequality (6.8) (Bubeck, arXiv:1405.4980v2, proof of Theorem 6.11, p. 346):
`1 − (2/π) arcsin(t) ≥ 0.878 (1 − t)` for all `t ∈ [−1, 1]`. -/
theorem eq_6_8 (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    1 - 2 / Real.pi * Real.arcsin t ≥ (0.878 : ℝ) * (1 - t) := by sorry

end ConvexOptAlg.GoemansWilliamson
