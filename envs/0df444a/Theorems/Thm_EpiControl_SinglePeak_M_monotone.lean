-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_M_monotone
-- name    : EpiControl.SinglePeak.M_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:38.177112+00:00
-- url     : https://prove2.me/theorems/157720ac-b359-4c14-a9ee-9531af347693
-- title:
--   Appendix A, p. 15 (PDF 16) — M(y) = min_{b∈B}[yb + c(b)] is non-decreasing
-- statement:
--   Let $M:\mathbb R\to\mathbb R$ be
--   $$M(y)=\min_{b\in B}\big[yb+c(b)\big],\qquad B=[\underline b,\bar b]\subset(0,\infty).$$
--   Under the standing assumptions, $M$ is non-decreasing on $\mathbb R$: $y\le y'$ implies $M(y)\le M(y')$.
--
--   Monotonicity of $M$ is used in Proposition 2 to compare the gain with its terminal value.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 15 (PDF 16), Appendix A, opening paragraph

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem M_monotone (P : Params) (hP : P.Standing) :
    Monotone P.M := by sorry
end EpiControl.SinglePeak
