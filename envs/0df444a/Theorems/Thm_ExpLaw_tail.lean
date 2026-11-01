-- Prove2me | Theorems.Thm_ExpLaw_tail
-- name    : ExpLaw.tail
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:19.146905+00:00
-- url     : https://prove2.me/theorems/1ff062f3-1c64-4337-9658-2416b6daf006
-- title:
--   Purchase probability under exponential valuations
-- statement:
--   Let $V$ be exponentially distributed with rate $l>0$. For every price $p\ge0$,
--   $$\Pr(V\ge p)=e^{-lp}.$$
--
--   This is the exponential demand model of Theorem 2 (p. 7) and Table 2 of the Online Appendix. It is one of the building blocks of the proof of Theorem 2 (p. 7; proof in Online Appendix A, p. 33).
--
--   **Formalization Note.** The law is Mathlib's `expMeasure l`.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; exponential demand model, Theorem 2, p. 7; Online Appendix, Table 2.

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ExpLaw

theorem tail {l p : ℝ} (hl : 0 < l) (hp : 0 ≤ p) :
    ((expMeasure l) (Set.Ici p)).toReal = Real.exp (-(l * p)) := by sorry

end ExpLaw
