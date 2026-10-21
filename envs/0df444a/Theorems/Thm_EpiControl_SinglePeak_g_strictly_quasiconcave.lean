-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_g_strictly_quasiconcave
-- name    : EpiControl.SinglePeak.g_strictly_quasiconcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:52.972896+00:00
-- url     : https://prove2.me/theorems/2f0a27cd-79ae-41c2-b08e-823d09beb578
-- title:
--   Proof of Proposition 7, p. 24 (PDF 25) — under Assumption 1 the gain g∗ is strictly quasi-concave (single-peaked)
-- statement:
--   Suppose Assumption 1 holds. Let $\beta^*$ be an optimal policy with SIR path $(s^*,i^*)$ and costate $\eta^*$ as in Proposition 1, let $g^*=\eta^*i^*s^*$, and suppose $\beta^*(t)\in\arg\min_{b\in B}[g^*(t)b+c(b)]$ for every $t\in[0,T]$. Then there is $t^*\in[0,T]$ such that
--   $$g^*\ \text{is strictly increasing on } [0,t^*]\quad\text{and strictly decreasing on } [t^*,T].$$
--
--   Combined with Proposition 2 (iii), this makes the optimal control quasi-convex, which is part (i) of Proposition 7.
--
--   **Formalization Note** The page concludes "$g^*$ is strictly quasi concave … let $t^*\in[0,T]$ be such that $g^*$ is strictly increasing on $[0,t^*]$ and strictly decreasing on $[t^*,T]$"; the statement is that form. The hypothesis that the argmin condition holds at every $t$ is the paper's convention (p. 7); $g^*$ itself does not depend on the version of $\beta^*$.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 24 (PDF 25), proof of Proposition 7

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem g_strictly_quasiconcave (P : Params) (hP : P.Standing) (dc : ℝ)
    (hA1 : P.Assumption1 dc) (β s i : ℝ → ℝ) (hopt : P.IsOptimal β s i) (η : ℝ → ℝ)
    (hη : P.IsCostate β s i η)
    (hconv : ∀ t ∈ Icc 0 P.T, P.ArgminAt (gain η s i t) (β t)) :
    ∃ tstar ∈ Icc 0 P.T,
      StrictMonoOn (gain η s i) (Icc 0 tstar) ∧ StrictAntiOn (gain η s i) (Icc tstar P.T) := by sorry
end EpiControl.SinglePeak
