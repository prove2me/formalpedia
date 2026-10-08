-- Prove2me | Theorems.Thm_DurrettProbability_brownian_positive_immediately
-- name    : DurrettProbability.brownian_positive_immediately
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T18:26:29.793906+00:00
-- url     : https://prove2.me/theorems/63d58763-2917-4b5b-8268-867e3af67060
-- title:
--   Theorem 7.2.4 — the path enters the positive half-line immediately
-- statement:
--   Let $B$ be a Brownian motion, so that $B_0=0$ almost surely. Then for almost every $\omega$ and
--   every real $\epsilon>0$ there is a time $t$ with
--   $$0<t<\epsilon\qquad\text{and}\qquad B_t(\omega)>0 .$$
--
--   In Durrett's notation, $\tau=\inf\{t\ge0:B_t>0\}$ satisfies $\mathbb P_0(\tau=0)=1$: the path
--   does not wait before becoming positive, however short the interval one looks at.
--
--   **Formalization Note** The statement is phrased through the witnessing times rather than through
--   an infimum, which avoids both the empty-set convention for $\inf$ and a coercion into the
--   extended reals; "$\tau=0$ almost surely" and "almost surely, every initial interval contains a
--   time where the path is positive" are the same assertion. The quantifier order places the null
--   set before $\epsilon$, so one path works for every $\epsilon$ at once.
--
--   The inequality on the value is strict, $B_t>0$ and not $B_t\ge0$, and the time is required to
--   be strictly positive, so the almost-sure value $B_0=0$ does not supply a witness.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 362 (PDF p. 370), Theorem 7.2.4: 'If tau = inf{t >= 0 : B_t > 0} then P_0(tau = 0) = 1.' Proof, p. 363 (PDF p. 371): 'P_0(tau <= t) >= P_0(B_t > 0) = 1/2 since the normal distribution is symmetric about 0. Letting t decrease to 0, we conclude P_0(tau = 0) = lim_{t down 0} P_0(tau <= t) >= 1/2, so it follows from Theorem 7.2.3 that P_0(tau = 0) = 1.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem brownian_positive_immediately {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ) < ε ∧ 0 < B t ω := by sorry

end DurrettProbability
