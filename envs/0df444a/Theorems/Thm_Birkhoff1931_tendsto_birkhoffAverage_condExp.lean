-- Prove2me | Theorems.Thm_Birkhoff1931_tendsto_birkhoffAverage_condExp
-- name    : Birkhoff1931.tendsto_birkhoffAverage_condExp
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:37:48.496064+00:00
-- url     : https://prove2.me/theorems/9af0260a-d09d-49f8-acd2-527b7042a0cc
-- title:
--   Birkhoff's pointwise ergodic theorem: $\frac1n\sum_{k<n} f\circ T^k \to \mathbb E[f\mid\mathcal I]$ almost everywhere
-- statement:
--   This is Birkhoff's pointwise ergodic theorem, in the probabilistic form that identifies the almost-everywhere limit as a conditional expectation.
--
--   Let $(X,\mathcal B,\mu)$ be a probability space and let $T : X \to X$ be a measure-preserving map: $T$ is measurable and $\mu(T^{-1}A) = \mu(A)$ for every $A \in \mathcal B$. Let
--
--   $$\mathcal I = \{A \in \mathcal B : T^{-1}A = A\}$$
--
--   be the $\sigma$-algebra of $T$-invariant sets. For a real-valued integrable function $f \in L^1(\mu)$, write $\mathbb E[f \mid \mathcal I]$ for the conditional expectation of $f$ given $\mathcal I$, and for $n \ge 1$ let
--
--   $$A_n f(x) = \frac{1}{n} \sum_{k=0}^{n-1} f\left(T^k x\right)$$
--
--   be the $n$-th Birkhoff (time) average of $f$ along the orbit of $x$. Then for $\mu$-almost every $x \in X$,
--
--   $$\lim_{n \to \infty} A_n f(x) = \mathbb E[f \mid \mathcal I](x).$$
--
--   This is the fundamental theorem of ergodic theory: time averages along almost every orbit converge, and the limit is the space average of $f$ over the invariant $\sigma$-algebra. When $T$ is ergodic, every invariant set has measure $0$ or $1$, so the limit is the constant $\int_X f \, d\mu$ almost everywhere. Applied to the shift map of a stationary sequence of random variables, it yields the strong law of large numbers for stationary sequences, and in particular Kolmogorov's strong law for i.i.d. sequences. Mathlib contains the von Neumann mean ergodic theorem ($L^2$ convergence) but not this pointwise result.
--
--   **Formalization Note** The average $A_n f$ is Mathlib's `birkhoffAverage ℝ T f n`, which equals $n^{-1} \sum_{k<n} f(T^{[k]} x)$ and takes the junk value $0$ at $n = 0$; this does not affect the limit. The invariant $\sigma$-algebra is `MeasurableSpace.invariants T`, consisting of the measurable sets $A$ with $T^{-1}A = A$ exactly. Some texts (e.g. Durrett) call a set invariant when $T^{-1}A = A$ up to a $\mu$-null set; for a measure-preserving $T$ every such set agrees with a strictly invariant set up to a null set, so both choices give the same conditional expectation $\mu$-almost everywhere. The conditional expectation is `MeasureTheory.condExp`, and the hypothesis $f \in L^1(\mu)$ is `Integrable f μ`. Only the almost-everywhere convergence is stated: the convergence $A_n f \to \mathbb E[f \mid \mathcal I]$ in $L^1(\mu)$, which Durrett's Theorem 6.2.1 also asserts, is not part of this statement, and neither is the ergodic special case.
-- source:
--   P. Walters, An Introduction to Ergodic Theory, GTM 79, Springer (1982), Theorem 1.14 (pointwise ergodic theorem: the averages converge a.e. to an invariant f* with the same integral); M. Einsiedler and T. Ward, Ergodic Theory with a view towards Number Theory, GTM 259, Springer (2011), Theorem 2.30 (pointwise ergodic theorem); R. Durrett, Probability: Theory and Examples, 5th ed., Cambridge University Press (2019), Theorem 6.2.1, whose almost-sure part identifies the limit as E(X | I): if phi is measure preserving on (Omega, F, P) and X is in L^1, then (1/n) sum_{m=0}^{n-1} X(phi^m omega) -> E(X | I) a.s. (Durrett also gives L^1 convergence, which is not included here; Theorem 7.2.1 in the 4th ed., 2010); G. D. Birkhoff, Proof of the ergodic theorem, Proc. Natl. Acad. Sci. USA 17 (1931), 656-660.

import Mathlib

namespace Birkhoff1931

open MeasureTheory Filter Topology

/-- **Birkhoff's pointwise ergodic theorem** (Walters, *An Introduction to Ergodic Theory*,
Theorem 1.14; Einsiedler–Ward, *Ergodic Theory with a view towards Number Theory*, Theorem 2.30;
in this conditional-expectation form, the almost-sure part of Durrett, *Probability: Theory and
Examples*, 5th ed., Theorem 6.2.1). Let `μ` be a probability measure on `X`, `T : X → X` a
measure-preserving map and `f ∈ L¹(μ)`. Then for `μ`-almost every `x` the Birkhoff averages
`(1/n) ∑_{k<n} f (T^[k] x)` converge to `μ[f | invariants T] x`, the conditional expectation of
`f` onto the σ-algebra of `T`-invariant sets. -/
theorem tendsto_birkhoffAverage_condExp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (T : X → X) (hT : MeasurePreserving T μ μ) (f : X → ℝ)
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffAverage ℝ T f n x) atTop
      (𝓝 (condExp (MeasurableSpace.invariants T) μ f x)) := by
  sorry

end Birkhoff1931
