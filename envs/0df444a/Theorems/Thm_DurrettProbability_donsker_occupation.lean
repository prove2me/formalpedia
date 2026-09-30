-- Prove2me | Theorems.Thm_DurrettProbability_donsker_occupation
-- name    : DurrettProbability.donsker_occupation
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-19T02:16:55.093727+00:00
-- url     : https://prove2.me/theorems/44a7e533-def6-4c9c-99bc-881730407b25
-- title:
--   Example 8.1.8 — occupation times of half-lines
-- statement:
--   Under the hypotheses of Durrett's Theorem 8.1.2, with $B$ a Brownian motion all of whose paths
--   are continuous, and for any real level $a$,
--   $$\frac1n\,\bigl|\{\,0\le m\le n:\ S_m>a\sqrt n\,\}\bigr|
--     \ \Longrightarrow\ \bigl|\{\,t\in[0,1]:\ B_t>a\,\}\bigr| ,$$
--   where $S_m=X_0+\dots+X_{m-1}$, the left-hand cardinality counts integer times, and the
--   right-hand $|\cdot|$ is Lebesgue measure.
--
--   At $a=0$ the limit law is the arcsine law, which is how Durrett's Theorem 4.9.6 for simple
--   random walk becomes a statement about every mean-zero, finite-variance walk. This is the
--   invariance principle of Erdős and Kac.
--
--   **Formalization Note** The count is written as a sum of indicator functions of $(a\sqrt n,\infty)$
--   evaluated at the partial sums, which equals the cardinality above and keeps a decidability side
--   condition out of the statement. The index $m$ runs over $0\le m\le n$, so $S_0=0$ is included;
--   it contributes exactly when $a\sqrt n<0$.
--
--   The limit is the Lebesgue measure of $\{t\in[0,1]:B_t>a\}$, converted from an extended
--   non-negative real to a real number. The conversion is harmless: the set sits inside $[0,1]$, so
--   its measure is at most $1$ and in particular finite. Times are matched to the process by taking
--   the non-negative part of $t$, which on $[0,1]$ is $t$ itself.
--
--   The strict inequality $B_t>a$ is the book's; the level set $\{B_t=a\}$ has measure zero almost
--   surely, which is exactly why the functional is almost surely continuous, so the strict and
--   non-strict versions have the same limit — but only the strict one is asserted here.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 393 (PDF p. 401), Example 8.1.8: 'Occupation times of half-lines. Let psi(omega) = |{t in [0,1] : omega(t) > a}|. ... Fubini''s theorem implies E_0|{t in [0,1] : B_t = a}| = integral_0^1 P_0(B_t = a) dt = 0 so psi is continuous P_0-a.s. Using Theorem 8.1.5, we now get that |{u <= n : S(u) > a sqrt(n)}|/n => |{t in [0,1] : B_t > a}|. As we will now show, with a little work, one can convert this into the more natural result |{m <= n : S_m > a sqrt(n)}|/n => |{t in [0,1] : B_t > a}|.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Definitions.Def_DurrettProbability_Donsker

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem donsker_occupation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P) (hint : Integrable (fun ω => X 0 ω ^ 2) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous fun t => B t ω)
    (a : ℝ) :
    TendstoInDistribution
      (fun n : ℕ => fun ω => (n : ℝ)⁻¹ * ∑ m ∈ Finset.range (n + 1),
        Set.indicator (Set.Ioi (a * Real.sqrt n)) (fun _ => (1 : ℝ))
          (∑ k ∈ Finset.range m, X k ω))
      atTop
      (fun ω => (volume {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ a < B t.toNNReal ω}).toReal)
      (fun _ => P) P' := by sorry

end DurrettProbability
