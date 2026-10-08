-- Prove2me | Theorems.Thm_DupacovaWets_Consistency_expectFn_proper_lsc
-- name    : DupacovaWets.Consistency.expectFn_proper_lsc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:06:22.018528+00:00
-- url     : https://prove2.me/theorems/d7e4a083-f472-4eb0-b8d4-0e40a6b0133a
-- title:
--   Lemma 3.6, p. 17 — a.s. Ef and every E^νf are proper, l.s.c., with domain S on which they are finite
-- statement:
--   The standing data are those of §3: $\Xi$ is a Polish space with its Borel $\sigma$-field, $P$ a probability measure on it, $(Z,\mathcal F,\mu)$ a probability space with an increasing sequence of sub-$\sigma$-fields $\mathcal F^1\subseteq\mathcal F^2\subseteq\dots\subseteq\mathcal F$, $P^\nu(\cdot,\zeta)$ random probability measures on $\Xi$, and $f:\mathbb R^n\times\Xi\to(-\infty,\infty]$ an integrand with domain $S\times\Xi$; $f$, $S$ and the measures satisfy Assumptions 3.4 and 3.5. Write $Ef(x)=\int_\Xi f(x,\xi)\,P(d\xi)$ and $E^\nu f(x,\zeta)=\int_\Xi f(x,\xi)\,P^\nu(d\xi,\zeta)$, with the $+\infty$ convention of p. 10.
--
--   Under Assumptions 3.4 and 3.5 there is $Z_0\in\mathcal F$ with $\mu(Z_0)=1$ such that for every $\zeta\in Z_0$ the functions $Ef$ and $E^\nu f(\cdot,\zeta)$, $\nu=1,2,\dots$, are proper and lower semicontinuous, and
--
--   $$
--   S=\operatorname{dom} Ef=\operatorname{dom} E^\nu f(\cdot,\zeta),
--   $$
--
--   with all these expectation functionals finite on $S$.
--
--   The lemma shows that the true and the estimated problems are well posed: their objectives are proper l.s.c. functions with the same effective domain $S$, the feasible set.
--
--   **Formalization Note** Lean writes $\mathbb R^n$ as `EuclideanSpace ℝ (Fin n)`, and the sample index is shifted: Lean's `Pν k ζ` and `𝔽 k` are the paper's $P^{k+1}(\cdot,\zeta)$ and $\mathcal F^{k+1}$, while $P = P^0$ is kept as the separate argument `P`. The paper also says that $\Xi$ is the support of $P$; this hypothesis is not used in the proofs of §3 and is omitted, which makes the statement stronger.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 17, Lemma 3.6

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
open MeasureTheory Filter Topology

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 17, Lemma 3.6: under Assumptions 3.4 and 3.5 there is
`Z₀ ∈ F` with `μ(Z₀) = 1` such that for every `ζ ∈ Z₀`, `Ef` and every `E^ν f(·, ζ)` are
proper lower semicontinuous functions with `S = dom Ef = dom E^ν f(·, ζ)`, finite on `S`.
(`Pν k` is the paper's `P^{k+1}`.) -/
theorem expectFn_proper_lsc {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν) :
    ∃ Z₀ : Set Z, MeasurableSet Z₀ ∧ μ Z₀ = 1 ∧ ∀ ζ ∈ Z₀,
      (IsProperFn (expectFn P f) ∧ LowerSemicontinuous (expectFn P f) ∧
        effDom (expectFn P f) = S ∧ ∀ x ∈ S, expectFn P f x ≠ ⊥ ∧ expectFn P f x ≠ ⊤) ∧
      ∀ k, IsProperFn (expectFn (Pν k ζ) f) ∧ LowerSemicontinuous (expectFn (Pν k ζ) f) ∧
        effDom (expectFn (Pν k ζ) f) = S ∧
        ∀ x ∈ S, expectFn (Pν k ζ) f x ≠ ⊥ ∧ expectFn (Pν k ζ) f x ≠ ⊤ := by sorry

end DupacovaWets.Consistency
