-- Prove2me | Theorems.Thm_ChenFarias_SimplePolicy_expected_max
-- name    : ChenFarias.SimplePolicy.expected_max
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:02:01.033913+00:00
-- url     : https://prove2.me/theorems/05040bfe-ad1f-421a-b1d3-452d846b91bb
-- title:
--   Proof of Lemma 9, p. 1131 — expectation of max{1, X/T}
-- statement:
--   If $X$ is exponentially distributed with rate $\beta>0$ and $T>0$, then
--
--   $$\mathbb E[\max\{1,X/T\}]=1+\frac{e^{-\beta T}}{\beta T}.$$
--
--   It supplies the constant $1+e^{-\beta T}/(\beta T)$ of Lemma 9.
--
--   **Formalization Note** This result does not depend on the pricing model. It uses Mathlib’s exponential law parameterized by rate $\beta$ and a lower integral in the extended nonnegative reals. Both divisions have strictly positive denominators.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), p. 1131, proof of Lemma 9, third display

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ChenFarias.SimplePolicy

/-- The third display in the proof of Lemma 9: the expectation under an
exponential law of rate `β`. -/
theorem expected_max (β T : ℝ) (hβ : 0 < β) (hT : 0 < T) :
    (∫⁻ s, ENNReal.ofReal (max 1 (s / T)) ∂expMeasure β) =
      ENNReal.ofReal (1 + Real.exp (-(β * T)) / (β * T)) := by sorry

end ChenFarias.SimplePolicy
