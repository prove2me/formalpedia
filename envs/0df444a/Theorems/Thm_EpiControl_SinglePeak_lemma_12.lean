-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_lemma_12
-- name    : EpiControl.SinglePeak.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:35.026319+00:00
-- url     : https://prove2.me/theorems/2c32e4c1-176f-488c-a39a-0200c2f2c342
-- title:
--   Lemma 12 (More Infected are Costly), p. 18 (PDF 19) — η∗(t) > 0 for all t ∈ [0, T)
-- statement:
--   Let $\beta^*$ be an optimal control with SIR path $(s^*,i^*)$ and multipliers $\lambda_1^*,\lambda_2^*$ as in Lemma 9, and put $\eta^*=\lambda_2^*-\lambda_1^*$. Then
--   $$\eta^*(t)>0\qquad\text{for all } t\in[0,T).$$
--
--   The marginal cost of infecting one more susceptible person is positive: the planner always benefits from fewer infected.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 18 (PDF 19), Lemma 12

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem lemma_12 (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (lam1 lam2 : ℝ → ℝ)
    (hlam : P.IsMultiplier β s i lam1 lam2) :
    ∀ t ∈ Ico 0 P.T, 0 < lam2 t - lam1 t := by sorry
end EpiControl.SinglePeak
