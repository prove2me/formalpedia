-- Prove2me | Theorems.Thm_AzumaWeightedSums_Multiplicative_lemma1_mgf_le
-- name    : AzumaWeightedSums.Multiplicative.lemma1_mgf_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:26:54.375859+00:00
-- url     : https://prove2.me/theorems/63ce5701-1069-4949-ad5d-840d0310c94f
-- title:
--   Lemma 1: moment-generating bound for class [M]
-- statement:
--   Let $(\Omega,\mathcal A,P)$ be a probability space and $(x_k)_{k\ge1}$ satisfy class [M] with $|x_k|\le1$ almost surely. For any $n\ge0$, any real weights $b_1,\ldots,b_n$, and any $t\in\mathbb R$,
--
--   $$
--   E\exp\!\left(t\sum_{k=1}^{n}b_kx_k\right)
--   \le
--   \exp\!\left(\frac{t^2}{2}\sum_{k=1}^{n}b_k^2\right).
--   $$
--
--   This is Azuma's Lemma 1. It supplies the exponential moment estimate used for the weighted almost-sure bound without requiring independence or symmetry.
--
--   **Formalization Note** The paper takes $n\ge1$; the empty-sum case $n=0$ is the valid identity $1\le1$. The exponential integrand is bounded and integrable because finitely many measurable variables are almost surely bounded by one.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 357, Lemma 1, (2.1), https://doi.org/10.2748/tmj/1178243286

import Mathlib
import Definitions.Def_AzumaWeightedSums_Multiplicative_IsMultiplicativeSystem

namespace AzumaWeightedSums.Multiplicative

open MeasureTheory

/-- Azuma (1967), p. 357, Lemma 1, (2.1), for one arbitrary row of weights. -/
theorem lemma1_mgf_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → ℝ) (hM : IsMultiplicativeSystem μ x)
    (n : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ∫ ω, Real.exp (t * ∑ k ∈ Finset.Icc 1 n, b k * x k ω) ∂μ ≤
      Real.exp ((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 n, (b k) ^ 2) := by sorry

end AzumaWeightedSums.Multiplicative
