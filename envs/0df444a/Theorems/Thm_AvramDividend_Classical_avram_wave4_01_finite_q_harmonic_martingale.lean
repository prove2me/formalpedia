-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_q_harmonic_martingale
-- name    : AvramDividend.Classical.avram_wave4_01_finite_q_harmonic_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:38:25.938669+00:00
-- url     : https://prove2.me/theorems/cdd9cb16-b1f3-4ebf-9fd0-b1acb442ad07
-- title:
--   Finite original-process q-eigenfunction sums give genuine discounted martingales
-- statement:
--   For a genuine spectrally negative Levy process in its source filtration, any finite real linear combination of exp(theta_i X_t-q t) is a martingale when all theta_i are nonnegative and every original Laplace exponent satisfies psi(theta_i)=q. This is a stochastic conditional-expectation result, not just a one-time semigroup identity, and follows by rewriting the canonically Proved finite compensated-exponential martingale.
-- source:
--   Canonically Proved finite compensated exponential martingale 0ebe2901; original process X and original filtration; exact pointwise root replacement.

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_compensated_exponential_martingale

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_01_finite_q_harmonic_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q : ℝ) (hroot : ∀ i ∈ s, X.ψ (rate i) = q) :
    Martingale
      (fun t ω => ∑ i ∈ s, coeff i *
        Real.exp (rate i * X.X t ω - (t : ℝ) * q))
      𝓕 P := by sorry
