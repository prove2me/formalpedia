-- Prove2me | Theorems.Thm_ExpLaw_cond_mean_below
-- name    : ExpLaw.cond_mean_below
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:18.994513+00:00
-- url     : https://prove2.me/theorems/c2fcbe2e-d34a-4cfc-9af6-2685604a0cdb
-- title:
--   No-purchase valuation under exponential valuations
-- statement:
--   Let $V$ be exponentially distributed with rate $l>0$. For every price $p>0$,
--   $$\mathbb E[V\mid V<p]=\frac1l-\frac{p}{e^{lp}-1}.$$
--
--   It is one of the building blocks of the proof of Theorem 2 (p. 7; proof in Online Appendix A, p. 33). Its derivative at the optimal price gives the entry $N_i'(p_i^*)$ of Table 3 (p. 34).
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; exponential demand model, Theorem 2, p. 7; Online Appendix, Tables 2 and 3.

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ExpLaw

theorem cond_mean_below {l p : ℝ} (hl : 0 < l) (hp : 0 < p) :
    (if (expMeasure l) (Set.Iio p) = 0 then 0
      else (∫ v in Set.Iio p, v ∂(expMeasure l)) / ((expMeasure l) (Set.Iio p)).toReal) =
      1 / l - p / (Real.exp (l * p) - 1) := by sorry

end ExpLaw
