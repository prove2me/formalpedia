-- Prove2me | Theorems.Thm_DupacovaWets_Consistency_expectFn_epiConverges
-- name    : DupacovaWets.Consistency.expectFn_epiConverges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:06:49.285603+00:00
-- url     : https://prove2.me/theorems/05019e53-96bb-4c61-949a-12a894556def
-- title:
--   Theorem 3.7, p. 18 — μ-a.s. the expectation functionals E^νf epi-converge and converge pointwise to Ef
-- statement:
--   The standing data are those of §3: $\Xi$ is a Polish space with its Borel $\sigma$-field, $P$ a probability measure on it, $(Z,\mathcal F,\mu)$ a probability space with an increasing sequence of sub-$\sigma$-fields $\mathcal F^1\subseteq\mathcal F^2\subseteq\dots\subseteq\mathcal F$, $P^\nu(\cdot,\zeta)$ random probability measures on $\Xi$, and $f:\mathbb R^n\times\Xi\to(-\infty,\infty]$ an integrand with domain $S\times\Xi$; $f$, $S$ and the measures satisfy Assumptions 3.4 and 3.5. Write $Ef(x)=\int_\Xi f(x,\xi)\,P(d\xi)$ and $E^\nu f(x,\zeta)=\int_\Xi f(x,\xi)\,P^\nu(d\xi,\zeta)$, with the $+\infty$ convention of p. 10.
--
--   Under Assumptions 3.4 and 3.5, for $\mu$-almost every $\zeta$,
--
--   $$
--   Ef=\operatorname{epi-lim}_{\nu\to\infty}E^\nu f(\cdot,\zeta)=\operatorname{ptwse-lim}_{\nu\to\infty}E^\nu f(\cdot,\zeta),
--   $$
--
--   that is, the estimated objectives epi-converge to $Ef$ and also $E^\nu f(x,\zeta)\to Ef(x)$ for every $x\in\mathbb R^n$.
--
--   This is the central approximation result of the paper: almost sure epi-convergence of the estimated objectives, from which consistency of optimal values and solutions follows through Proposition 3.3.
--
--   **Formalization Note** Lean writes $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, and the sample index is shifted: Lean's `Pν k ζ` and `𝔽 k` are the paper's $P^{k+1}(\cdot,\zeta)$ and $\mathcal F^{k+1}$, while $P = P^0$ is kept as the separate argument `P`. The pointwise limit is taken in $[-\infty,\infty]$ with its order topology (off $S$ both sides equal $+\infty$). The paper also says that $\Xi$ is the support of $P$; this hypothesis is not used in the proofs of §3 and is omitted, which makes the statement stronger.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 18, Theorem 3.7

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
open MeasureTheory Filter Topology

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 18, Theorem 3.7: under Assumptions 3.4 and 3.5, `μ`-almost
surely `Ef = epi-lim E^ν f = ptwse-lim E^ν f`. (`Pν k` is the paper's `P^{k+1}`.) -/
theorem expectFn_epiConverges {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν) :
    ∀ᵐ ζ ∂μ, EpiConverges (fun k => expectFn (Pν k ζ) f) (expectFn P f) ∧
      ∀ x, Tendsto (fun k => expectFn (Pν k ζ) f x) atTop (𝓝 (expectFn P f x)) := by sorry

end DupacovaWets.Consistency
