-- Prove2me | Theorems.Thm_DurrettProbability_donsker_continuous_mapping
-- name    : DurrettProbability.donsker_continuous_mapping
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-19T02:15:53.363894+00:00
-- url     : https://prove2.me/theorems/c98dc977-403d-4dc4-b626-4f8e0c6ad08c
-- title:
--   Theorem 8.1.5 — continuous mapping for almost surely continuous functionals
-- statement:
--   Let $X_0,X_1,\dots$ be measurable, jointly independent, all with the law of $X_0$, with
--   $$\mathbb E X_0=0,\qquad \mathbb E X_0^2=1,$$
--   the square being integrable. Let $B$ be a Brownian motion on a second probability space, every
--   one of whose paths is continuous, and write $W_n=S(n\cdot)/\sqrt n$ and $B(\cdot)$ for the
--   associated random elements of $C[0,1]$.
--
--   Let $\psi:C[0,1]\to\mathbb R$ be measurable, and suppose $\psi$ is **continuous at almost every
--   Brownian path**: for almost every $\omega$, $\psi$ is continuous at the point $B(\cdot)(\omega)$
--   of $C[0,1]$. Then
--   $$\psi(W_n)\ \Longrightarrow\ \psi(B(\cdot)).$$
--
--   This is the Mann–Wald continuous mapping theorem in the form that tolerates discontinuities,
--   provided they form a set of limit-law measure zero — which is what makes it usable for the
--   maximum, the occupation time, and the last zero.
--
--   **Formalization Note** Continuity is required only at the points where the *limit* law lives,
--   and only almost everywhere with respect to it; $\psi$ may be wildly discontinuous elsewhere.
--   Measurability of $\psi$ is assumed separately, since almost-everywhere continuity with respect
--   to a measure does not by itself give Borel measurability of the map on the whole space.
--
--   Convergence in distribution is weak convergence of the push-forward laws, here of real random
--   variables on possibly different probability spaces. The hypotheses on the walk are those of
--   Durrett's Theorem 8.1.2, carried through unchanged: i.i.d. with mean $0$ and variance $1$.
--
--   Assuming every Brownian path is continuous, rather than almost every one, is what makes
--   $B(\cdot)$ a $C[0,1]$-valued random variable at all; it costs nothing, since a Brownian motion
--   may be modified on a null set to achieve it.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 392 (PDF p. 400), Theorem 8.1.5: 'If psi : C[0,1] -> R has the property that it is continuous P_0-a.s. then psi(S(n.)/sqrt(n)) => psi(B(.)).' Introduced as: 'The key to each one is a consequence of the following result which follows from Theorem 3.10.1.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Definitions.Def_DurrettProbability_Donsker

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem donsker_continuous_mapping
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P) (hint : Integrable (fun ω => X 0 ω ^ 2) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous fun t => B t ω)
    (ψ : PathSpace → ℝ) (hψm : Measurable ψ)
    (hψ : ∀ᵐ ω ∂P', ContinuousAt ψ (brownianPath B ω)) :
    TendstoInDistribution (fun n : ℕ => fun ω => ψ (walkPath X n ω)) atTop
      (fun ω => ψ (brownianPath B ω)) (fun _ => P) P' := by sorry

end DurrettProbability
