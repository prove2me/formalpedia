-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_eq_3_6
-- name    : CvitanicKaratzas92.Optimality.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:50:21.079215+00:00
-- url     : https://prove2.me/theorems/ede26215-2ab8-44be-8cac-95c1f8663ef5
-- title:
--   Section 3, (3.6) — the budget constraint $E[H_0(T)X(T)+\int_0^TH_0c\,dt]\le x$ on $\mathcal A_0(x)$
-- statement:
--   Under the standing assumptions of the paper, let $x>0$ and let $(\pi,c)\in\mathcal A_0(x)$ with wealth process $X^{x,\pi,c}$. Then
--   $$E\Big[H_0(T)X^{x,\pi,c}(T)+\int_0^TH_0(t)c(t)\,dt\Big]\le x,$$
--   where $H_0=\gamma_0Z_0$ is the state-price density (2.10).
--
--   This is the static budget constraint of the original market: the process $H_0X+\int_0^\cdot H_0c\,ds$ is a nonnegative local martingale, hence a supermartingale. It is the basic inequality behind Lemma 7.2.
--
--   **Formalization Note** The expectation is the Lebesgue integral of a nonnegative quantity (a.s. $X\ge0$).
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 771, Section 3, (3.6)

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Section 3, (3.6), p. 771: for every `(π, c) ∈ 𝒜₀(x)` with wealth
`X`, `E[H₀(T)X(T) + ∫₀ᵀ H₀(t)c(t) dt] ≤ x`. -/
theorem eq_3_6 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2)
    (x : ℝ) (hx : 0 < x) (τ : Triple Ω d) (hτ : τ ∈ A0 P 𝓕 T I M x) :
    ∫⁻ ω, (ENNReal.ofReal (H0 I M T ω * τ.X T ω) +
      ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (H0 I M s.toNNReal ω * τ.c s.toNNReal ω)) ∂P ≤
      ENNReal.ofReal x := by sorry


end CvitanicKaratzas92.Optimality
