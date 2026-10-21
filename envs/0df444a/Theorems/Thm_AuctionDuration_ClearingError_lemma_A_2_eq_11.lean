-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_lemma_A_2_eq_11
-- name    : AuctionDuration.ClearingError.lemma_A_2_eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:55.638368+00:00
-- url     : https://prove2.me/theorems/71e63552-f206-407f-a54e-bf634e898e18
-- title:
--   Lemma A.2 (11), p. 21 — E[1_{N_t>0}/N_t] and E[1_{N_t>0}/N_t²] for a Poisson count
-- statement:
--   Let $N_t$ be a Poisson random variable with mean $m_t\ge0$ (for instance, the value at time $t$ of an inhomogeneous Poisson process with intensity measure $\lambda$, with $m_t=\int_0^t\lambda(ds)$). Then
--   $$\mathbb E\Big[\frac{\mathbf 1_{N_t>0}}{N_t}\Big]=e^{-m_t}\int_0^{m_t}\frac{e^s-1}{s}\,ds,\qquad \mathbb E\Big[\frac{\mathbf 1_{N_t>0}}{N_t^2}\Big]=e^{-m_t}\int_0^{m_t}\frac1s\int_0^s\frac{e^u-1}{u}\,du\,ds .$$
--
--   These inverse moments give the functions $f$ and $\ell$ of the reduction (8) in closed form.
--
--   **Formalization Note** The lemma is stated for a general inhomogeneous Poisson process, but only the law of $N_t$ enters; the Lean statement takes a measurable $\mathbb N$-valued $N$ with law $\mathrm{Poisson}(m)$, $m\in\mathbb R_{\ge0}$. The integrands $(e^s-1)/s$ and $\frac1s\int_0^s\cdots$ are $0$ at $s=0$ in Lean (division by zero), a single point that does not affect the interval integrals.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, p. 21, Lemma A.2, (11)

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model

namespace AuctionDuration.ClearingError
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Lemma A.2, p. 21, (11): if N_t is Poisson with mean m_t, then
E[1_{N_t>0}/N_t] = e^{−m_t} ∫_0^{m_t} (e^s − 1)/s ds and
E[1_{N_t>0}/N_t²] = e^{−m_t} ∫_0^{m_t} (1/s) ∫_0^s (e^u − 1)/u du ds. -/
theorem lemma_A_2_eq_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N) (m : ℝ≥0) (hlaw : P.map N = poissonMeasure m) :
    ∫ ω, (if 0 < N ω then 1 / (N ω : ℝ) else 0) ∂P =
        Real.exp (-(m : ℝ)) * ∫ s in (0 : ℝ)..(m : ℝ), (Real.exp s - 1) / s ∧
    ∫ ω, (if 0 < N ω then 1 / (N ω : ℝ) ^ 2 else 0) ∂P =
        Real.exp (-(m : ℝ)) *
          ∫ s in (0 : ℝ)..(m : ℝ), (1 / s) * ∫ u in (0 : ℝ)..s, (Real.exp u - 1) / u := by sorry

end AuctionDuration.ClearingError
