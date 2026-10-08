-- Prove2me | Theorems.Thm_DupacovaWets_Consistency_expectFn_epigraph_measurable
-- name    : DupacovaWets.Consistency.expectFn_epigraph_measurable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:06:58.271987+00:00
-- url     : https://prove2.me/theorems/915f7cca-1dea-4b20-b06c-9f53a636990a
-- title:
--   Theorem 3.8, p. 20 — μ-a.s. the E^νf are random l.s.c. functions with F^ν-measurable epigraphs
-- statement:
--   The standing data are those of §3: $\Xi$ is a Polish space with its Borel $\sigma$-field, $P$ a probability measure on it, $(Z,\mathcal F,\mu)$ a probability space with an increasing sequence of sub-$\sigma$-fields $\mathcal F^1\subseteq\mathcal F^2\subseteq\dots\subseteq\mathcal F$, $P^\nu(\cdot,\zeta)$ random probability measures on $\Xi$, and $f:\mathbb R^n\times\Xi\to(-\infty,\infty]$ an integrand with domain $S\times\Xi$; $f$, $S$ and the measures satisfy Assumptions 3.4 and 3.5. Write $Ef(x)=\int_\Xi f(x,\xi)\,P(d\xi)$ and $E^\nu f(x,\zeta)=\int_\Xi f(x,\xi)\,P^\nu(d\xi,\zeta)$, with the $+\infty$ convention of p. 10.
--
--   Under Assumptions 3.4 and 3.5 there is $Z_0\in\mathcal F$ with $\mu(Z\setminus Z_0)=0$ such that for every $\nu=1,2,\dots$:
--
--   1. for every $\zeta\in Z_0$ the epigraph $\operatorname{epi}E^\nu f(\cdot,\zeta)\subseteq\mathbb R^n\times\mathbb R$ is nonempty and closed;
--   2. the multifunction $\zeta\mapsto\operatorname{epi}E^\nu f(\cdot,\zeta): Z_0\rightrightarrows\mathbb R^n\times\mathbb R$ is $\mathcal F^\nu$-measurable.
--
--   Together these say that, almost surely, $E^\nu f$ is a random lower semicontinuous function (normal integrand) adapted to the information $\mathcal F^\nu$ available at stage $\nu$; this is what makes the estimated optimal values and solution sets measurable.
--
--   **Formalization Note** Lean writes $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, and the sample index is shifted: Lean's `Pν k ζ` and `𝔽 k` are the paper's $P^{k+1}(\cdot,\zeta)$ and $\mathcal F^{k+1}$, while $P = P^0$ is kept as the separate argument `P`. "Random lower semicontinuous function" is encoded by the equivalent conditions (3.4i)–(3.4ii) of p. 11 (nonempty closed-valued, measurable epigraphical multifunction), which is what the paper's proof establishes. Since the exceptional null set $Z\setminus Z_0$ lies in $\mathcal F$ but not necessarily in $\mathcal F^\nu$, "$\mathcal F^\nu$-measurable on $Z_0$" is read in the trace $\sigma$-field $\{Z_0\cap B : B\in\mathcal F^\nu\}$ (`IsMeasurableMultifunctionOn`). The paper also says that $\Xi$ is the support of $P$; this hypothesis is not used in the proofs of §3 and is omitted, which makes the statement stronger.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 20, Theorem 3.8, via (3.4i)–(3.4ii) of p. 11

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
import Definitions.Def_DupacovaWets_Consistency_Multifunction
open MeasureTheory Filter Topology

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 20, Theorem 3.8, in the form (3.4i)–(3.4ii) of p. 11: there is
`Z₀ ∈ F` with `μ(Z \ Z₀) = 0` such that for every `ν` and every `ζ ∈ Z₀` the epigraph
`epi E^ν f(·, ζ)` is nonempty and closed, and `ζ ↦ epi E^ν f(·, ζ) : Z₀ ⇉ ℝⁿ × ℝ` is
`F^ν`-measurable (trace σ-algebra on `Z₀`). (`Pν k`, `𝔽 k` are `P^{k+1}`, `F^{k+1}`.) -/
theorem expectFn_epigraph_measurable {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν) :
    ∃ Z₀ : Set Z, MeasurableSet Z₀ ∧ μ Z₀ᶜ = 0 ∧
      (∀ ζ ∈ Z₀, ∀ k, (epigraph (expectFn (Pν k ζ) f)).Nonempty ∧
        IsClosed (epigraph (expectFn (Pν k ζ) f))) ∧
      ∀ k, IsMeasurableMultifunctionOn (𝔽 k) Z₀ (fun ζ => epigraph (expectFn (Pν k ζ) f)) := by sorry

end DupacovaWets.Consistency
