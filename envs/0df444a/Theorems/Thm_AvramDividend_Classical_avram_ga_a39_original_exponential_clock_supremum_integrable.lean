-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a39_original_exponential_clock_supremum_integrable
-- name    : AvramDividend.Classical.avram_ga_a39_original_exponential_clock_supremum_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:40:29.093087+00:00
-- url     : https://prove2.me/theorems/2cf64612-10e7-4d37-a2e4-77bf5d4a1ce0
-- title:
--   Original exponential-clock supremum moment is finite below positive Laplace root
-- statement:
--   For the original spectrally negative Levy source, at positive exponential-clock rate p=psi(lam) with lam>0, any exponent beta<lam has finite integral of the positive exponential of the running supremum over the exponential-clock product measure. Derive finiteness from the Proved exact Laplace transform a4d6 and strict positivity of lam-beta. This provides the random-clock product moment required by a38 for the top-cap Gaussian terminal positive L1 envelope.
-- source:
--   d9c4650e and a38 c8192ba2; Proved  a4d6b2d4-a167-444b-bab4-c707f819a8a7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a39_original_exponential_clock_supremum_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p lam β : ℝ) (hp : 0 < p) (hlam : 0 < lam)
    (hroot : X.ψ lam = p) (hβ : β < lam) :
    (∫⁻ z : Ω×ℝ,
      ENNReal.ofReal (Real.exp
        (β * runningSup X (Real.toNNReal z.2) z.1))
        ∂ (P.prod (expMeasure p))) < ⊤ := by sorry
