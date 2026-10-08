-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_eq_9_4
-- name    : CvitanicKaratzas92.Optimality.eq_9_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:13:29.615915+00:00
-- url     : https://prove2.me/theorems/3fa64fea-fa51-4881-bf3e-230ac8d08c8f
-- title:
--   Section 9, (9.4) — $E[H_\nu(T)X(T)+\int_0^TH_\nu c\,ds]\le x$ for $K$-valued admissible portfolios and every $\nu\in\mathcal D$
-- statement:
--   Under the standing assumptions, let $x>0$ and let $(\pi,c)\in\mathcal A_0(x)$ satisfy
--   $$\pi(t,\omega)\in K\quad\text{for }\ell\otimes P\text{-a.e. }(t,\omega). \tag{9.1}$$
--   Then, with $X=X^{x,\pi,c}$ the wealth process in $\mathcal M$,
--   $$E\Big[H_\nu(T)X^{x,\pi,c}(T)+\int_0^TH_\nu(s)c(s)\,ds\Big]\le x\qquad\forall\,\nu\in\mathcal D. \tag{9.4}$$
--
--   Every constrained policy satisfies the budget constraint of every auxiliary market, since $\delta(\nu)+\pi^*\nu\ge0$ for $\pi\in K$; this is the necessity half of the hedging Theorem 9.1 and the reason (B) implies (E).
--
--   **Formalization Note** The expectation is the Lebesgue integral of a nonnegative quantity.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 780, Section 9, (9.1), (9.4)

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Section 9, (9.4), p. 780: for `(π, c) ∈ 𝒜₀(x)` with (9.1)
`π ∈ K` `ℓ ⊗ P`-a.e., and every `ν ∈ 𝒟`, `E[H_ν(T)X(T) + ∫₀ᵀ H_ν(s)c(s) ds] ≤ x`. -/
theorem eq_9_4 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (x : ℝ) (hx : 0 < x) (τ : Triple Ω d) (hτ : τ ∈ A0 P 𝓕 T I M x)
    (h91 : ∀ᵐ q ∂(lebP P T), τ.π q.1.toNNReal q.2 ∈ K)
    (ν : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hν : IsD P 𝓕 T K ν) :
    ∫⁻ ω, (ENNReal.ofReal (HNu I M K ν T ω * τ.X T ω) +
      ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (HNu I M K ν s.toNNReal ω * τ.c s.toNNReal ω)) ∂P ≤
      ENNReal.ofReal x := by sorry


end CvitanicKaratzas92.Optimality
