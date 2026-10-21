-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_lemma_11
-- name    : EpiControl.SinglePeak.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:34.342175+00:00
-- url     : https://prove2.me/theorems/de19c476-8f8d-43cb-8376-ba30342f91a5
-- title:
--   Lemma 11 (first part), pp. 16–17 (PDF 17–18) — η∗ = λ∗₂ − λ∗₁ solves the reduced adjoint equation (18)
-- statement:
--   Let $\beta^*$ be an optimal control with SIR path $(s^*,i^*)$ and multipliers $\lambda_1^*,\lambda_2^*$ as in Lemma 9, and put $\eta^*=\lambda_2^*-\lambda_1^*$. Then $\eta^*(T)=\frac{v(i^*(T))}{\gamma i^*(T)}$ and $\eta^*$ solves
--   $$(\eta^*)'(t)=\eta^*(t)\beta^*(t)i^*(t)-v'(i^*(t))+\frac{v(i^*(t))+c(\beta^*(t))-M\big(v(i^*(T))s^*(T)/\gamma\big)}{i^*(t)}. \tag{18}$$
--
--   The two multipliers thus collapse into one costate, whose equation no longer involves $\lambda_1^*,\lambda_2^*$.
--
--   **Formalization Note** (18) is stated in integral form on $[0,T]$ from the terminal value. Only the first sentence of Lemma 11 is formalized; the converse (19)–(20) is not used later.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), pp. 16–17 (PDF 17–18), Lemma 11, (18)

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem lemma_11 (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (lam1 lam2 : ℝ → ℝ)
    (hlam : P.IsMultiplier β s i lam1 lam2) :
    lam2 P.T - lam1 P.T = P.v (i P.T) / (P.γ * i P.T) ∧
    ∀ t ∈ Icc 0 P.T,
      lam2 t - lam1 t = (lam2 P.T - lam1 P.T) - ∫ r in t..P.T,
        ((lam2 r - lam1 r) * β r * i r - deriv P.v (i r) +
          (P.v (i r) + P.c (β r) - P.M (P.v (i P.T) * s P.T / P.γ)) / i r) := by sorry
end EpiControl.SinglePeak
