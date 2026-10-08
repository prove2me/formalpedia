-- Prove2me | Theorems.Thm_DupacovaWets_Consistency_argmin_measurable
-- name    : DupacovaWets.Consistency.argmin_measurable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:07:40.389075+00:00
-- url     : https://prove2.me/theorems/3b9a4fcc-bf40-4227-97e1-72c5be60e353
-- title:
--   Theorem 3.9 (ii), p. 22 — a.s. ζ ↦ argmin E^νf(·, ζ) is a closed-valued F^ν-measurable multifunction
-- statement:
--   The standing data are those of §3: $\Xi$ is a Polish space with its Borel $\sigma$-field, $P$ a probability measure on it, $(Z,\mathcal F,\mu)$ a probability space with an increasing sequence of sub-$\sigma$-fields $\mathcal F^1\subseteq\mathcal F^2\subseteq\dots\subseteq\mathcal F$, $P^\nu(\cdot,\zeta)$ random probability measures on $\Xi$, and $f:\mathbb R^n\times\Xi\to(-\infty,\infty]$ an integrand with domain $S\times\Xi$; $f$, $S$ and the measures satisfy Assumptions 3.4 and 3.5. Write $Ef(x)=\int_\Xi f(x,\xi)\,P(d\xi)$ and $E^\nu f(x,\zeta)=\int_\Xi f(x,\xi)\,P^\nu(d\xi,\zeta)$, with the $+\infty$ convention of p. 10.
--
--   Under Assumptions 3.4 and 3.5 there is $Z_0\in\mathcal F$ with $\mu(Z\setminus Z_0)=0$ such that for every $\nu=1,2,\dots$ the multifunction
--
--   $$
--   \zeta\mapsto\operatorname{argmin}E^\nu f(\cdot,\zeta): Z_0\rightrightarrows\mathbb R^n
--   $$
--
--   is closed-valued and $\mathcal F^\nu$-measurable.
--
--   Measurability of the estimated solution sets is what allows one to choose estimators $x^\nu(\zeta)$ that depend measurably on the data seen up to stage $\nu$.
--
--   **Formalization Note** Lean writes $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, and the sample index is shifted: Lean's `Pν k ζ` and `𝔽 k` are the paper's $P^{k+1}(\cdot,\zeta)$ and $\mathcal F^{k+1}$, while $P = P^0$ is kept as the separate argument `P`. Since the exceptional null set $Z\setminus Z_0$ lies in $\mathcal F$ but not necessarily in $\mathcal F^\nu$, "$\mathcal F^\nu$-measurable on $Z_0$" is read in the trace $\sigma$-field $\{Z_0\cap B : B\in\mathcal F^\nu\}$ (`IsMeasurableMultifunctionOn`). The paper also says that $\Xi$ is the support of $P$; this hypothesis is not used in the proofs of §3 and is omitted, which makes the statement stronger.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 22, Theorem 3.9 (ii)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
import Definitions.Def_DupacovaWets_Consistency_Multifunction
open MeasureTheory Filter Topology

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 22, Theorem 3.9 (ii): there is `Z₀ ∈ F` with `μ(Z \ Z₀) = 0`
such that for every `ν`, `ζ ↦ argmin E^ν f(·, ζ) : Z₀ ⇉ ℝⁿ` is closed-valued and
`F^ν`-measurable (trace σ-algebra on `Z₀`). (`Pν k`, `𝔽 k` are `P^{k+1}`, `F^{k+1}`.) -/
theorem argmin_measurable {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν) :
    ∃ Z₀ : Set Z, MeasurableSet Z₀ ∧ μ Z₀ᶜ = 0 ∧
      (∀ ζ ∈ Z₀, ∀ k, IsClosed (argminSet (expectFn (Pν k ζ) f))) ∧
      ∀ k, IsMeasurableMultifunctionOn (𝔽 k) Z₀ (fun ζ => argminSet (expectFn (Pν k ζ) f)) := by sorry

end DupacovaWets.Consistency
