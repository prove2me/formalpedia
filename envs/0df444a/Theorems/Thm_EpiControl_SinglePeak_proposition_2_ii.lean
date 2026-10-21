-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_proposition_2_ii
-- name    : EpiControl.SinglePeak.proposition_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:48.245025+00:00
-- url     : https://prove2.me/theorems/404adeeb-73ba-49b1-a537-a36d3f5b2e51
-- title:
--   Proposition 2 (ii), p. 7 (PDF 8) — bounds (8): 0 < g∗(T) < g∗(t) < (1/γ)[v(1) + v′(1)(e^{(T−t)γ} − 1)]
-- statement:
--   Let $\beta^*$ be an optimal policy with SIR path $(s^*,i^*)$ and costate $\eta^*$ as in Proposition 1, and let $g^*=\eta^*i^*s^*$. For every $t\in[0,T)$,
--   $$0<g^*(T)<g^*(t)<\frac1\gamma\Big[v(1)+v'(1)\big(e^{(T-t)\gamma}-1\big)\Big]. \tag{8}$$
--
--   The incentive to reduce transmission is always larger than at the vaccine date, and bounded by an explicit exponential.
--
--   **Formalization Note** $v'(1)$ is the derivative at $1$ of the $C^1$ extension of $v$, which agrees with the page's one-sided derivative.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 7 (PDF 8), Proposition 2 (ii), (8)

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem proposition_2_ii (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η) :
    ∀ t ∈ Ico 0 P.T,
      0 < gain η s i P.T ∧ gain η s i P.T < gain η s i t ∧
      gain η s i t <
        1 / P.γ * (P.v 1 + deriv P.v 1 * (Real.exp ((P.T - t) * P.γ) - 1)) := by sorry
end EpiControl.SinglePeak
