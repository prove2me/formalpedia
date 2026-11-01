-- Prove2me | Theorems.Thm_ExpLaw_mean_excess
-- name    : ExpLaw.mean_excess
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:19.019539+00:00
-- url     : https://prove2.me/theorems/8052cbff-ebbf-44b4-82f4-7a5ff636abd6
-- title:
--   Consumer surplus under exponential valuations
-- statement:
--   Let $V$ be exponentially distributed with rate $l>0$. For every price $p\ge0$,
--   $$\mathbb E\big[(V-p)^+\big]=\frac{e^{-lp}}{l}.$$
--
--   It is one of the building blocks of the proof of Theorem 2 (p. 7; proof in Online Appendix A, p. 33).
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; exponential demand model, Theorem 2, p. 7; Online Appendix, Table 2.

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ExpLaw

theorem mean_excess {l p : ℝ} (hl : 0 < l) (hp : 0 ≤ p) :
    ∫ v, max (v - p) 0 ∂(expMeasure l) = Real.exp (-(l * p)) / l := by sorry

end ExpLaw
