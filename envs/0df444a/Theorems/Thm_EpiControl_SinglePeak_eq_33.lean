-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_eq_33
-- name    : EpiControl.SinglePeak.eq_33
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:43.799976+00:00
-- url     : https://prove2.me/theorems/872656bf-4e7b-4c56-a194-19884c42cfa5
-- title:
--   (33), p. 23 (PDF 24) — s²(1 − s) ≤ 4/27 on [0, 1], hence (s∗(t))² i∗(t) ≤ 4/27
-- statement:
--   For every $x\in[0,1]$,
--   $$x^2(1-x)\le\frac{4}{27}.$$
--   Consequently, for an optimal control and its SIR path $(s^*,i^*)$, which satisfies $s^*(t)+i^*(t)\le 1$, and every $t\in[0,T]$,
--   $$s^*(t)^2\,i^*(t)\le s^*(t)^2\big(1-s^*(t)\big)\le\frac{4}{27}. \tag{33}$$
--
--   The constant $4/27$ is where the factor $27/4$ of Assumption 1 comes from.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 23 (PDF 24), proof of Proposition 7, (33)

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem eq_33 (P : Params) (hP : P.Standing) :
    (∀ x ∈ Icc (0 : ℝ) 1, x ^ 2 * (1 - x) ≤ 4 / 27) ∧
    ∀ β s i : ℝ → ℝ, P.IsOptimal β s i →
      ∀ t ∈ Icc 0 P.T, s t ^ 2 * i t ≤ s t ^ 2 * (1 - s t) ∧ s t ^ 2 * (1 - s t) ≤ 4 / 27 := by sorry
end EpiControl.SinglePeak
