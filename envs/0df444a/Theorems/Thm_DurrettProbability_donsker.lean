-- Prove2me | Theorems.Thm_DurrettProbability_donsker
-- name    : DurrettProbability.donsker
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-19T02:18:22.473693+00:00
-- url     : https://prove2.me/theorems/fc196840-1e82-44c1-9a67-52d879a8272f
-- title:
--   Theorem 8.1.4 — Donsker's theorem
-- statement:
--   Let $X_0,X_1,\dots$ be measurable real random variables on a probability space, jointly
--   independent, each with the law of $X_0$, satisfying
--   $$\mathbb E X_0=0,\qquad \mathbb E X_0^2=1,$$
--   with $X_0^2$ integrable. Let $S_m=X_0+\dots+X_{m-1}$, let $S(u)$ be the polygonal path agreeing
--   with $S_m$ at integer times and linear in between, and set
--   $$W_n(t)=\frac{S(nt)}{\sqrt n},\qquad t\in[0,1],$$
--   a random element of $C[0,1]$.
--
--   Let $B$ be a Brownian motion on a second probability space, every one of whose paths is
--   continuous, and let $B(\cdot)$ be its restriction to $[0,1]$, also a random element of $C[0,1]$.
--
--   Then
--   $$W_n\ \Longrightarrow\ B(\cdot),$$
--   meaning that the laws of $W_n$ on $C[0,1]$ converge weakly to the law of $B(\cdot)$.
--
--   The space $C[0,1]$ carries the topology of uniform convergence and its Borel $\sigma$-algebra,
--   so this is convergence of measures on an infinite-dimensional function space, not convergence of
--   finite-dimensional marginals. That is precisely the content beyond the central limit theorem,
--   which is the case of evaluation at $t=1$.
--
--   **Formalization Note** Indexing runs from zero, so $S_0=0$ and the walk's $m$-th partial sum
--   uses $X_0,\dots,X_{m-1}$; independence is joint independence of the whole family, not pairwise.
--   Identical distribution is stated as each $X_k$ having the same law as $X_0$, and the mean and
--   variance are moments of $X_0$.
--
--   The interpolation is a finite sum of clamped linear pieces, so no continuity side condition
--   accompanies the definition of $W_n$; it is an element of $C[0,1]$ by construction. At $n=0$ the
--   rescaling divides by $\sqrt0=0$, giving the zero path, which does not affect a limit along
--   $n\to\infty$.
--
--   Every path of $B$ is assumed continuous, not merely almost every one. This is what makes
--   $B(\cdot)$ a genuine $C[0,1]$-valued random variable, and it is no restriction: a Brownian
--   motion may be modified on a null set to have all paths continuous, and Durrett's construction on
--   $C[0,\infty)$ has the property by definition.
--
--   Existence of a Brownian motion is a hypothesis here, not a claim; producing one is the content
--   of Durrett's Theorem 7.1.1, which the ambient library does not supply.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 392 (PDF p. 400), Theorem 8.1.4: 'Donsker''s theorem. Under the hypotheses of Theorem 8.1.2, S(n.)/sqrt(n) => B(.), i.e., the associated measures on C[0,1] converge weakly.' The hypotheses of Theorem 8.1.2, p. 391 (PDF p. 399): 'Let X_1, X_2, ... be i.i.d. with a distribution F, which has mean 0 and variance 1, and let S_n = X_1 + ... + X_n.' The interpolation, same page: 'Let N be the nonnegative integers and let S(u) = S_k if u = k in N, linear on [k, k+1] for k in N.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Definitions.Def_DurrettProbability_Donsker

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem donsker {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hint : Integrable (fun ω => X 0 ω ^ 2) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous fun t => B t ω) :
    TendstoInDistribution (fun n : ℕ => walkPath X n) atTop (brownianPath B)
      (fun _ => P) P' := by sorry

end DurrettProbability
