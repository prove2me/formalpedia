-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f5_topcap_analytic_HJB_global_exponential_growth
-- name    : AvramDividend.Classical.avram_p4_f5_topcap_analytic_HJB_global_exponential_growth
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T07:31:28.991198+00:00
-- url     : https://prove2.me/theorems/51922c24-523b-4637-a780-8f4ef5a2923a
-- title:
--   Deterministic original nonzero-Gaussian Lévy HJB supersolution exponential upper growth
-- statement:
--   Under original spectral-negative Lévy, standing conditions, nonzero Gaussian coefficient, and arbitrary nonnegative-gradient HJB supersolution with unbounded cap, establish a global exponential upper envelope. No stopped process, cash or strategy assumptions appear.
-- source:
--   Genuine analytic source separating generator comparison from original stopped stochastic cash bookkeeping.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_p4_f5_topcap_analytic_HJB_global_exponential_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) := by sorry
