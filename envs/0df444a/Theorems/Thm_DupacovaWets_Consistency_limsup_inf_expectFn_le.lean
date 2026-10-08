-- Prove2me | Theorems.Thm_DupacovaWets_Consistency_limsup_inf_expectFn_le
-- name    : DupacovaWets.Consistency.limsup_inf_expectFn_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:07:07.131766+00:00
-- url     : https://prove2.me/theorems/7f48d600-17b9-40fc-adb5-88dec1318bf6
-- title:
--   Theorem 3.9, (3.14), p. 21 — μ-a.s. limsup of the estimated optimal values ≤ inf Ef
-- statement:
--   The standing data are those of §3: $\Xi$ is a Polish space with its Borel $\sigma$-field, $P$ a probability measure on it, $(Z,\mathcal F,\mu)$ a probability space with an increasing sequence of sub-$\sigma$-fields $\mathcal F^1\subseteq\mathcal F^2\subseteq\dots\subseteq\mathcal F$, $P^\nu(\cdot,\zeta)$ random probability measures on $\Xi$, and $f:\mathbb R^n\times\Xi\to(-\infty,\infty]$ an integrand with domain $S\times\Xi$; $f$, $S$ and the measures satisfy Assumptions 3.4 and 3.5. Write $Ef(x)=\int_\Xi f(x,\xi)\,P(d\xi)$ and $E^\nu f(x,\zeta)=\int_\Xi f(x,\xi)\,P^\nu(d\xi,\zeta)$, with the $+\infty$ convention of p. 10.
--
--   Under Assumptions 3.4 and 3.5, for $\mu$-almost every $\zeta$,
--
--   $$
--   \limsup_{\nu\to\infty}\,\bigl(\inf E^\nu f(\cdot,\zeta)\bigr)\le\inf Ef . \tag{3.14}
--   $$
--
--   The estimated optimal values are thus asymptotically no worse than the true optimal value; this is the first assertion of the paper's consistency theorem.
--
--   **Formalization Note** Lean writes $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, and the sample index is shifted: Lean's `Pν k ζ` and `𝔽 k` are the paper's $P^{k+1}(\cdot,\zeta)$ and $\mathcal F^{k+1}$, while $P = P^0$ is kept as the separate argument `P`. Infima are over all of $\mathbb R^n$, in $[-\infty,\infty]$. The paper also says that $\Xi$ is the support of $P$; this hypothesis is not used in the proofs of §3 and is omitted, which makes the statement stronger.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 21, Theorem 3.9, (3.14)

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
open MeasureTheory Filter Topology

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 21, Theorem 3.9, (3.14): under Assumptions 3.4 and 3.5,
`μ`-almost surely `limsup (inf E^ν f) ≤ inf Ef`. (`Pν k` is the paper's `P^{k+1}`.) -/
theorem limsup_inf_expectFn_le {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν) :
    ∀ᵐ ζ ∂μ, limsup (fun k => ⨅ x, expectFn (Pν k ζ) f x) atTop ≤ ⨅ x, expectFn P f x := by sorry

end DupacovaWets.Consistency
