-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_gaussian_gradient_finite_base_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_compact_gaussian_gradient_finite_base_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:42:33.655198+00:00
-- url     : https://prove2.me/theorems/6cf097b2-a68b-4b12-b9f9-4a32c992a883
-- title:
--   Original Gaussian derivative coefficient has finite L² energy on a finite compact localisation
-- statement:
--   For the genuine original spectrally negative Levy process X with its intrinsic Gaussian volatility sigma, C2 smoothness of w on the exact strict HJB cap gives a finite bound on (sigma w'(U))² over every finite source localisation measure whenever U remains in [delta,K] with 0<delta<=K<C. This is only coefficient energy, and asserts neither a separately constructed Brownian process nor a terminal martingale.
-- source:
--   Apply the already Proved source-exact strict-cap derivative compact bound 2dd46d99. Multiply by the original X.sigma, square the uniform absolute bound, and integrate against any finite localisation measure. The result is a physical continuous-Gaussian L2 prerequisite; same-source martingale extraction and Ito-Meyer remain explicit separate obligations.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_compact_gaussian_gradient_finite_base_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    {S : Type*} [mS : MeasurableSpace S]
    (μ : Measure S) (hμ : μ Set.univ < ⊤)
    (U : S → ℝ) (hU : ∀ s, U s ∈ Icc δ K) :
    (∫⁻ s, ENNReal.ofReal ((X.σ * deriv w (U s)) ^ 2) ∂μ) < ⊤ := by sorry
