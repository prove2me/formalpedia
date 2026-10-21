-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_lemma_A_2_eq_12
-- name    : AuctionDuration.ClearingError.lemma_A_2_eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:56.894144+00:00
-- url     : https://prove2.me/theorems/0ffe280b-721d-4090-8796-f8573f641e91
-- title:
--   Lemma A.2 (12), p. 21 — E[1/(1+N_t)²] and E[1/(2+N_t)²] for a Poisson count
-- statement:
--   Let $N_t$ be a Poisson random variable with mean $m_t>0$ (for instance, the value at time $t$ of an inhomogeneous Poisson process with intensity measure $\lambda$, with $m_t=\int_0^t\lambda(ds)$). Then
--   $$\mathbb E\Big[\frac1{(1+N_t)^2}\Big]=\frac{e^{-m_t}}{m_t}\int_0^{m_t}\frac{e^s-1}{s}\,ds,\qquad \mathbb E\Big[\frac1{(2+N_t)^2}\Big]=\frac1{m_t^2}\Big(1-e^{-m_t}-e^{-m_t}\int_0^{m_t}\frac{e^s-1}{s}\,ds\Big).$$
--
--   Combined with Lemma A.1 these identities give the price-move function $g$ in closed form.
--
--   **Formalization Note** Only the law of $N_t$ enters; the Lean statement takes a measurable $\mathbb N$-valued $N$ with law $\mathrm{Poisson}(m)$. The hypothesis $m>0$ is added: the page divides by $m_t$, and at $m_t=0$ the right-hand sides are undefined.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, p. 21, Lemma A.2, (12)

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model

namespace AuctionDuration.ClearingError
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Lemma A.2, p. 21, (12): if N_t is Poisson with mean m_t > 0, then
E[1/(1 + N_t)²] = (e^{−m_t}/m_t) ∫_0^{m_t} (e^s − 1)/s ds and
E[1/(2 + N_t)²] = (1/m_t²)(1 − e^{−m_t} − e^{−m_t} ∫_0^{m_t} (e^s − 1)/s ds). -/
theorem lemma_A_2_eq_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N) (m : ℝ≥0) (hm : 0 < m) (hlaw : P.map N = poissonMeasure m) :
    ∫ ω, 1 / (1 + (N ω : ℝ)) ^ 2 ∂P =
        Real.exp (-(m : ℝ)) / (m : ℝ) * ∫ s in (0 : ℝ)..(m : ℝ), (Real.exp s - 1) / s ∧
    ∫ ω, 1 / (2 + (N ω : ℝ)) ^ 2 ∂P =
        1 / (m : ℝ) ^ 2 * (1 - Real.exp (-(m : ℝ)) -
          Real.exp (-(m : ℝ)) * ∫ s in (0 : ℝ)..(m : ℝ), (Real.exp s - 1) / s) := by sorry

end AuctionDuration.ClearingError
