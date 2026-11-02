-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
-- name    : AvramDividend.Classical.avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:36:34.255848+00:00
-- url     : https://prove2.me/theorems/1a3ddaf1-be03-43cf-b243-90c0e71248d4
-- title:
--   Actual original dividend jump has cap-linear value drop at least its payment, including time zero and simultaneous jumps
-- statement:
--   For every admissible actual dividend strategy and any permitted payment time, including time zero, chronological right-dividend atom δ at original riskProcess U has cap-linear verification drop V(U)-V(U-δ) at least δ. Admissibility supplies postpayment solvency; rightLimit nonnegativity gives the ordered segment; the proved global cap-linear secant proves the inequality without a cap on the time-zero reserve. Original X_t can already include a source jump before the right payment. No finite-jump, smooth-dividend, or interior-reserve restriction.
-- source:
--   Full original source IsAdmissibleLe and actual rightLimit dividend payment, with Proved avram_wave5_04b_positive_ennreal_cap_extension_global_secant. This complements positive-time pointwise w-drop without assuming initial reserve below cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω ≤
      V (riskProcess X x D t ω) -
        V (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) := by sorry
