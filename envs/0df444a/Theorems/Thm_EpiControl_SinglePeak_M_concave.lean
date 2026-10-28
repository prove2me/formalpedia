-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_M_concave
-- name    : EpiControl.SinglePeak.M_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:52.31939+00:00
-- url     : https://prove2.me/theorems/3eb11b62-390a-4644-a448-072384bf6ed7
-- title:
--   Proof of Proposition 7, p. 23 (PDF 24) — M(y) = min_{b∈B}[yb + c(b)] is concave
-- statement:
--   Let $M:\mathbb R\to\mathbb R$ be
--   $$M(y)=\min_{b\in B}\big[yb+c(b)\big],\qquad B=[\underline b,\bar b]\subset(0,\infty).$$
--   Under the standing assumptions, $M$ is concave on $\mathbb R$.
--
--   Concavity of $M$ gives the bound (34) in the proof of Proposition 7, which feeds into the second-derivative inequality (37).
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 23 (PDF 24), proof of Proposition 7, sentence before (34)

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem M_concave (P : Params) (hP : P.Standing) :
    ConcaveOn ℝ univ P.M := by sorry
end EpiControl.SinglePeak
