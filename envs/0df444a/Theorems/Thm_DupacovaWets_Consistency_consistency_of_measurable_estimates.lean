-- Prove2me | Theorems.Thm_DupacovaWets_Consistency_consistency_of_measurable_estimates
-- name    : DupacovaWets.Consistency.consistency_of_measurable_estimates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:07:31.984437+00:00
-- url     : https://prove2.me/theorems/b1603c16-30bf-4f84-99f4-2ffcb8c8235c
-- title:
--   Theorem 3.9 (Consistency), pp. 21–22 — measurable optimal estimates converge μ-a.s. to the unique minimizer in D
-- statement:
--   The standing data are those of §3: $\Xi$ is a Polish space with its Borel $\sigma$-field, $P$ a probability measure on it, $(Z,\mathcal F,\mu)$ a probability space with an increasing sequence of sub-$\sigma$-fields $\mathcal F^1\subseteq\mathcal F^2\subseteq\dots\subseteq\mathcal F$, $P^\nu(\cdot,\zeta)$ random probability measures on $\Xi$, and $f:\mathbb R^n\times\Xi\to(-\infty,\infty]$ an integrand with domain $S\times\Xi$; $f$, $S$ and the measures satisfy Assumptions 3.4 and 3.5. Write $Ef(x)=\int_\Xi f(x,\xi)\,P(d\xi)$ and $E^\nu f(x,\zeta)=\int_\Xi f(x,\xi)\,P^\nu(d\xi,\zeta)$, with the $+\infty$ convention of p. 10.
--
--   Suppose Assumptions 3.4 and 3.5 hold and there is a compact set $D\subseteq\mathbb R^n$ such that for every $\nu=1,2,\dots$ the set $(\operatorname{argmin}E^\nu f)\cap D$ is nonempty $\mu$-almost surely, and
--
--   $$
--   \{x^*\}=\operatorname{argmin}Ef\cap D .
--   $$
--
--   Then there exist $\mathcal F^\nu$-measurable selections $x^\nu$ of $\operatorname{argmin}E^\nu f$ such that
--
--   $$
--   x^*=\lim_{\nu\to\infty}x^\nu(\zeta)\quad\text{for }\mu\text{-almost all }\zeta,
--   $$
--
--   and also $\inf Ef=\lim_{\nu\to\infty}(\inf E^\nu f)$ $\mu$-almost surely.
--
--   This is the strong consistency statement of the paper: estimators that use only the information available at stage $\nu$ and solve the estimated problem converge almost surely to the true solution, and the estimated optimal values converge to the true optimal value. It extends Wald's and Huber's consistency theorems to constrained problems with extended-real-valued, merely lower semicontinuous criteria.
--
--   **Formalization Note** Lean writes $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, and the sample index is shifted: Lean's `Pν k ζ` and `𝔽 k` are the paper's $P^{k+1}(\cdot,\zeta)$ and $\mathcal F^{k+1}$, while $P = P^0$ is kept as the separate argument `P`. The paper's selections are maps $x^\nu:Z_0\to\mathbb R^n$, measurable for the trace of $\mathcal F^\nu$ on a full-measure set $Z_0$; here they are total maps $x^\nu:Z\to\mathbb R^n$, $\mathcal F^\nu$-measurable on all of $Z$, with $x^\nu(\zeta)\in\operatorname{argmin}E^\nu f(\cdot,\zeta)$ for all $\nu$ for $\mu$-almost every $\zeta$. The two forms are equivalent: a function into $\mathbb R^n$ that is measurable for a trace $\sigma$-field extends measurably to the whole space, and $Z_0$ has full measure. The limit of the infima is in $[-\infty,\infty]$. The paper also says that $\Xi$ is the support of $P$; this hypothesis is not used in the proofs of §3 and is omitted, which makes the statement stronger.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), pp. 21–22, Theorem 3.9, 'In particular' conclusion

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
open MeasureTheory Filter Topology

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), pp. 21–22, Theorem 3.9 (Consistency), "In particular": under
Assumptions 3.4 and 3.5, if `D ⊆ ℝⁿ` is compact, `(argmin E^ν f) ∩ D` is nonempty `μ`-a.s. for
every `ν`, and `{x*} = argmin Ef ∩ D`, then there are `F^ν`-measurable selections `x^ν` of
`argmin E^ν f` with `x^ν(ζ) → x*` for `μ`-almost all `ζ`, and `inf E^ν f → inf Ef` `μ`-a.s.
(`Pν k`, `𝔽 k`, `x k` are the paper's `P^{k+1}`, `F^{k+1}`, `x^{k+1}`.) -/
theorem consistency_of_measurable_estimates {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : IsCompact D)
    (hDne : ∀ k, ∀ᵐ ζ ∂μ, (argminSet (expectFn (Pν k ζ) f) ∩ D).Nonempty)
    (xstar : EuclideanSpace ℝ (Fin n)) (hx : argminSet (expectFn P f) ∩ D = {xstar}) :
    (∃ x : ℕ → Z → EuclideanSpace ℝ (Fin n), (∀ k, Measurable[𝔽 k] (x k)) ∧
        (∀ᵐ ζ ∂μ, ∀ k, x k ζ ∈ argminSet (expectFn (Pν k ζ) f)) ∧
        (∀ᵐ ζ ∂μ, Tendsto (fun k => x k ζ) atTop (𝓝 xstar))) ∧
      ∀ᵐ ζ ∂μ, Tendsto (fun k => ⨅ y, expectFn (Pν k ζ) f y) atTop (𝓝 (⨅ y, expectFn P f y)) := by sorry

end DupacovaWets.Consistency
