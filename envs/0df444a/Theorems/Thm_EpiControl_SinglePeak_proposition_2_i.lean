-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_proposition_2_i
-- name    : EpiControl.SinglePeak.proposition_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:38.488674+00:00
-- url     : https://prove2.me/theorems/92504a59-fe8b-4f80-9eb5-1261663aacbb
-- title:
--   Proposition 2 (i), p. 7 (PDF 8) — the gain g∗ = η∗i∗s∗ evolves according to (7)
-- statement:
--   Let $\beta^*$ be an optimal policy with SIR path $(s^*,i^*)$ and costate $\eta^*$ as in Proposition 1, and let $g^*(t)=\eta^*(t)i^*(t)s^*(t)$ be the gain from reducing the transmission rate. Then for every $t\in[0,T]$
--   $$(g^*)'(t)=-\gamma g^*(t)+s^*(t)\Big(M(g^*(t))-M(g^*(T))-\big[v'(i^*(t))i^*(t)-v(i^*(t))\big]\Big), \tag{7}$$
--   with terminal condition $g^*(T)=\frac1\gamma\big[v(i^*(T))s^*(T)\big]$.
--
--   Equation (7) is a closed equation for the gain along the optimal path; all later results on the shape of the optimal policy come from it.
--
--   **Formalization Note** The derivative is taken within $[0,T]$ (one-sided at the endpoints) and holds at **every** $t$: the right-hand side of (7) is continuous, as the proof of Proposition 7 uses.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 7 (PDF 8), Proposition 2 (i), (7)

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem proposition_2_i (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η) :
    (∀ t ∈ Icc 0 P.T,
      HasDerivWithinAt (gain η s i)
        (-P.γ * gain η s i t + s t * (P.M (gain η s i t) - P.M (gain η s i P.T) -
          (deriv P.v (i t) * i t - P.v (i t)))) (Icc 0 P.T) t) ∧
    gain η s i P.T = 1 / P.γ * (P.v (i P.T) * s P.T) := by sorry
end EpiControl.SinglePeak
