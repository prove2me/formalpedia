-- Prove2me | Theorems.Thm_DurrettProbability_brownian_holder
-- name    : DurrettProbability.brownian_holder
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-18T18:25:02.68762+00:00
-- url     : https://prove2.me/theorems/529b4db9-0c6f-4af4-a844-b30c1b2f0e40
-- title:
--   Theorem 7.1.5 — Brownian paths are Hölder continuous of every exponent below 1/2
-- statement:
--   Let $B$ be a Brownian motion on a probability space $(\Omega,\mathcal F,\mathbb P)$: its
--   finite-dimensional laws are those of Brownian motion and almost every path is continuous. Let
--   $\gamma$ be a non-negative real with $0<\gamma<1/2$.
--
--   Then for $\mathbb P$-almost every $\omega$ and **every** $T\ge0$ there is a constant $C$ with
--   $$|B_t(\omega)-B_s(\omega)|\ \le\ C\,|t-s|^{\gamma}\qquad\text{for all }s,t\in[0,T].$$
--
--   The null set is chosen before $T$: a single path satisfies the estimate on every bounded initial
--   interval, with a constant that may grow with $T$.
--
--   **Formalization Note** Hölder continuity is stated on $[0,T]$ rather than on $[0,\infty)$
--   because the global statement is false — the constant genuinely must depend on the interval. The
--   estimate is Mathlib's Hölder-on-a-set predicate, phrased with extended distances, which on the
--   reals is the displayed inequality.
--
--   The exponent is a non-negative real and both bounds are strict, so the borderline exponent
--   $1/2$ is excluded, as it must be: Durrett records that $\mathbb P(t\in H_{1/2})=0$ for each
--   fixed $t$. No claim is made about exponents above $1/2$, where the conclusion is false.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 358 (PDF p. 366), Theorem 7.1.5: 'Brownian paths are Hoelder continuous for any exponent gamma < 1/2.' The derivation on the same page: 'The scaling relation, (7.1.1), implies E|B_t - B_s|^{2m} = C_m |t - s|^m where C_m = E|B_1|^{2m}, so using Theorem 7.1.3 with beta = 2m, alpha = m - 1 and letting m -> infinity gives a result of Wiener (1923).' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem brownian_holder {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ2 : γ < 1 / 2) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ C : ℝ≥0,
      HolderOnWith C γ (fun t : ℝ≥0 => B t ω) (Set.Iic T) := by sorry

end DurrettProbability
