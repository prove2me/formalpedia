-- Prove2me | Theorems.Thm_DupacovaWets_Consistency_clusterPt_mem_argmin
-- name    : DupacovaWets.Consistency.clusterPt_mem_argmin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:07:10.561717+00:00
-- url     : https://prove2.me/theorems/f3232290-43eb-417e-9415-84047f079cd1
-- title:
--   Theorem 3.9 (i), p. 21 — a.s. every cluster point of estimated optimal solutions minimizes Ef
-- statement:
--   The standing data are those of §3: $\Xi$ is a Polish space with its Borel $\sigma$-field, $P$ a probability measure on it, $(Z,\mathcal F,\mu)$ a probability space with an increasing sequence of sub-$\sigma$-fields $\mathcal F^1\subseteq\mathcal F^2\subseteq\dots\subseteq\mathcal F$, $P^\nu(\cdot,\zeta)$ random probability measures on $\Xi$, and $f:\mathbb R^n\times\Xi\to(-\infty,\infty]$ an integrand with domain $S\times\Xi$; $f$, $S$ and the measures satisfy Assumptions 3.4 and 3.5. Write $Ef(x)=\int_\Xi f(x,\xi)\,P(d\xi)$ and $E^\nu f(x,\zeta)=\int_\Xi f(x,\xi)\,P^\nu(d\xi,\zeta)$, with the $+\infty$ convention of p. 10.
--
--   Under Assumptions 3.4 and 3.5 there is $Z_0\in\mathcal F$ with $\mu(Z\setminus Z_0)=0$ such that for every $\zeta\in Z_0$: if $x^\nu\in\operatorname{argmin}E^\nu f(\cdot,\zeta)$ for $\nu=1,2,\dots$, then every cluster point $\hat x$ of $(x^\nu)$ satisfies
--
--   $$
--   \hat x\in\operatorname{argmin} Ef ,
--   $$
--
--   i.e. it is an optimal solution of the true problem.
--
--   This is the solution part of the consistency theorem, valid without assuming that $Ef$ has a unique minimizer.
--
--   **Formalization Note** Lean writes $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, and the sample index is shifted: Lean's `Pν k ζ` and `𝔽 k` are the paper's $P^{k+1}(\cdot,\zeta)$ and $\mathcal F^{k+1}$, while $P = P^0$ is kept as the separate argument `P`. A cluster point is a point $\hat x$ such that every neighbourhood of $\hat x$ contains $x^\nu$ for infinitely many $\nu$ (`MapClusterPt`). On the page (i) and (ii) share one set $Z_0$; as separate items each has its own, and intersecting the two recovers a common one. The printed "$\operatorname{argmin}E^\nu f^\nu$" is read as $\operatorname{argmin}E^\nu f$. The paper also says that $\Xi$ is the support of $P$; this hypothesis is not used in the proofs of §3 and is omitted, which makes the statement stronger.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 21, Theorem 3.9 (i)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
open MeasureTheory Filter Topology

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 21, Theorem 3.9 (i): there is `Z₀ ∈ F` with `μ(Z \ Z₀) = 0`
such that for every `ζ ∈ Z₀`, every cluster point of every sequence `x^ν ∈ argmin E^ν f(·, ζ)`
belongs to `argmin Ef`. (`Pν k` is the paper's `P^{k+1}`.) -/
theorem clusterPt_mem_argmin {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν) :
    ∃ Z₀ : Set Z, MeasurableSet Z₀ ∧ μ Z₀ᶜ = 0 ∧ ∀ ζ ∈ Z₀,
      ∀ xs : ℕ → EuclideanSpace ℝ (Fin n), (∀ k, xs k ∈ argminSet (expectFn (Pν k ζ) f)) →
        ∀ xhat : EuclideanSpace ℝ (Fin n), MapClusterPt xhat atTop xs →
          xhat ∈ argminSet (expectFn P f) := by sorry

end DupacovaWets.Consistency
