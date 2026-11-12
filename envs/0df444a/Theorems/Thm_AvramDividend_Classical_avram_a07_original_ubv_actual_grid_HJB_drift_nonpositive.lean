-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_original_ubv_actual_grid_HJB_drift_nonpositive
-- name    : AvramDividend.Classical.avram_a07_original_ubv_actual_grid_HJB_drift_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:33:28.206248+00:00
-- url     : https://prove2.me/theorems/fdc3cc06-8e68-466a-8313-c5ffb893bc26
-- title:
--   Actual original reserve finite-grid discounted HJB and payment drift nonpositive
-- statement:
--   At every sampled pre-ruin interior reserve, the source generator inequality and gradient constraint make each chronological discounted interval drift plus dividend-consumption contribution nonpositive. This is the deterministic finite-grid drift component of the original controlled Ito-Meyer proof, independent of noise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_original_ubv_actual_grid_HJB_drift_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (s : ℕ → ℝ≥0) (hMono : Monotone s)
    (N : ℕ) (ω : Ω)
    (hInside : ∀ i < N, 0 < riskProcess X x D (s i) ω ∧
      ENNReal.ofReal (riskProcess X x D (s i) ω) < C)
    (hPay : ∀ i < N, D (s i) ω ≤ D (s (i + 1)) ω) :
    (∑ i ∈ Finset.range N,
      Real.exp (-(q * (s i : ℝ))) *
        (((s (i + 1) : ℝ) - (s i : ℝ)) *
          (X.generator w (riskProcess X x D (s i) ω) -
            q * w (riskProcess X x D (s i) ω)) +
        (D (s (i + 1)) ω - D (s i) ω) *
          (1 - deriv w (riskProcess X x D (s i) ω)))) ≤ 0 := by sorry
