-- Prove2me | Theorems.Thm_DurrettProbability_brownian_zeros_accumulate
-- name    : DurrettProbability.brownian_zeros_accumulate
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T18:27:00.771543+00:00
-- url     : https://prove2.me/theorems/b730c894-0b11-4d98-b71f-7d8b837d165e
-- title:
--   Theorem 7.2.5 — the zero set accumulates at time zero
-- statement:
--   Let $B$ be a Brownian motion. Then for almost every $\omega$ and every real $\epsilon>0$ there
--   is a time $t$ with
--   $$0<t<\epsilon\qquad\text{and}\qquad B_t(\omega)=0 .$$
--
--   In Durrett's notation, $T_0=\inf\{t>0:B_t=0\}$ satisfies $\mathbb P_0(T_0=0)=1$: zero is an
--   accumulation point of the zero set from the right, so "the first return to zero" is not a
--   meaningful notion at time $0$.
--
--   **Formalization Note** As with Theorem 7.2.4 the infimum is replaced by its witnesses, and the
--   time is required to be strictly positive, so the almost-sure value $B_0=0$ is excluded as a
--   witness — without that requirement the statement would be trivially true. The equality
--   $B_t(\omega)=0$ is exact, not approximate. The null set is quantified before $\epsilon$.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 363 (PDF p. 371), Theorem 7.2.5: 'If T_0 = inf{t > 0 : B_t = 0} then P_0(T_0 = 0) = 1.' The sentence preceding it: 'Once Brownian motion must hit (0, infinity) immediately starting from 0, it must also hit (-infinity, 0) immediately. Since t -> B_t is continuous, this forces:' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem brownian_zeros_accumulate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ) < ε ∧ B t ω = 0 := by sorry

end DurrettProbability
