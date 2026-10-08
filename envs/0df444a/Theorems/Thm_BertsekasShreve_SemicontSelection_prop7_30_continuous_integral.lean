-- Prove2me | Theorems.Thm_BertsekasShreve_SemicontSelection_prop7_30_continuous_integral
-- name    : BertsekasShreve.SemicontSelection.prop7_30_continuous_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:46.349895+00:00
-- url     : https://prove2.me/theorems/7e52a23d-0a93-459b-946e-93553b36efdb
-- title:
--   Proposition 7.30 — integrating a bounded continuous function against a continuous kernel gives a continuous function
-- statement:
--   Let $X$ and $Y$ be separable metrizable spaces, let $P(Y)$ be the space of Borel probability measures on $Y$ with the weak topology, and let $q(dy\mid x)$ be a **continuous stochastic kernel** on $Y$ given $X$, i.e. a continuous map $x\mapsto q(dy\mid x)$ from $X$ to $P(Y)$. If $f$ is a bounded continuous real-valued function on $X\times Y$, then the function $\lambda:X\to\mathbb R$,
--
--   $$\lambda(x)=\int f(x,y)\,q(dy\mid x),$$
--
--   is continuous.
--
--   The result is the continuous base case from which the semicontinuity of integrals of semicontinuous functions (Proposition 7.31) is obtained.
--
--   **Formalization Note** $P(Y)$ is Mathlib's `ProbabilityMeasure Y` with its topology of weak convergence (convergence of integrals of bounded continuous functions), and $Y$ carries its Borel σ-algebra. "Separable metrizable" is `MetrizableSpace` plus `SeparableSpace`.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 145, Proposition 7.30; Definition 7.12, p. 134

import Mathlib

namespace BertsekasShreve.SemicontSelection

open MeasureTheory TopologicalSpace

/-- Proposition 7.30 (Bertsekas & Shreve, p. 145). Let `X`, `Y` be separable metrizable spaces and
`q(dy|x)` a continuous stochastic kernel on `Y` given `X` (a continuous map `X → P(Y)`, `P(Y)` with
the weak topology). If `f` is a bounded continuous real function on `X × Y`, then
`λ(x) = ∫ f(x, y) q(dy|x)` is continuous. -/
theorem prop7_30_continuous_integral {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (q : X → ProbabilityMeasure Y) (hq : Continuous q) (f : BoundedContinuousFunction (X × Y) ℝ) :
    Continuous (fun x => ∫ y, f (x, y) ∂(q x : Measure Y)) := by sorry

end BertsekasShreve.SemicontSelection
