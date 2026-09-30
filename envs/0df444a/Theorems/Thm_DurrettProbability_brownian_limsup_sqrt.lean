-- Prove2me | Theorems.Thm_DurrettProbability_brownian_limsup_sqrt
-- name    : DurrettProbability.brownian_limsup_sqrt
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-18T18:27:31.961962+00:00
-- url     : https://prove2.me/theorems/09f66952-464e-42b8-bbe4-19800d4d5e6a
-- title:
--   Theorem 7.2.8 — the path oscillates on the scale of the square root
-- statement:
--   Let $B$ be a Brownian motion. Then for almost every $\omega$:
--
--   1. for every real $K$ there are arbitrarily large times $t$ with
--      $$\frac{B_t(\omega)}{\sqrt t}>K,$$
--   2. and for every real $K$ there are arbitrarily large times $t$ with
--      $$\frac{B_t(\omega)}{\sqrt t}<K .$$
--
--   These two say $\limsup_{t\to\infty}B_t/\sqrt t=+\infty$ and
--   $\liminf_{t\to\infty}B_t/\sqrt t=-\infty$: the path, rescaled by its standard deviation, does
--   not settle anywhere but sweeps out the whole line infinitely often.
--
--   **Formalization Note** "Arbitrarily large times" is the frequently-along-the-at-infinity-filter
--   quantifier, so each clause says: for every $T$ there is $t\ge T$ with the stated inequality.
--   This is exactly what $\limsup=+\infty$ and $\liminf=-\infty$ mean, and it avoids stating a
--   $\limsup$ valued in the extended reals with the coercion that would require.
--
--   The null set is quantified before $K$, so a single path works for every $K$ in both clauses.
--   The quotient at $t=0$ is $0/0=0$ by the convention for division in the reals, which is
--   irrelevant to a statement along the filter of large times.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 364 (PDF p. 372), Theorem 7.2.8: 'Let B_t be a one-dimensional Brownian motion starting at 0 then with probability 1, lim sup_{t -> infinity} B_t/sqrt(t) = infinity, lim inf_{t -> infinity} B_t/sqrt(t) = -infinity.' Proof: 'Let K < infinity. By Exercise 2.3.1 and scaling P_0(B_n/sqrt(n) >= K i.o.) >= lim sup_n P_0(B_n >= K sqrt(n)) = P_0(B_1 >= K) > 0, so the 0-1 law in Theorem 7.2.7 implies the probability is 1. Since K is arbitrary, this proves the first result. The second one follows from symmetry.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem brownian_limsup_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, (∀ K : ℝ, ∃ᶠ t : ℝ≥0 in atTop, K < B t ω / Real.sqrt t)
      ∧ (∀ K : ℝ, ∃ᶠ t : ℝ≥0 in atTop, B t ω / Real.sqrt t < K) := by sorry

end DurrettProbability
