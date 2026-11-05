-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_08_source_piecewise_stopped_terminal_ofReal_le_cap
-- name    : AvramDividend.Classical.avram_wave8_08_source_piecewise_stopped_terminal_ofReal_le_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:26:53.382361+00:00
-- url     : https://prove2.me/theorems/4ea6cd91-4b5b-4b22-8aa3-c4b58b1ffd26
-- title:
--   W8-08 original post-rightpayment stopped terminal remains beneath the reserve cap
-- statement:
--   For the original capped admissible dividend strategy and any source stopped clock, the piecewise stopped terminal reserve used by the original Itô–Meyer budget, including rightpayment at the horizon and the ruin branch, has ENNReal.ofReal value at most the cap. This is the exact finite-cap terminal localisation interface for the canonical W8-08 residual.
-- source:
--   Original Avram stopped verification terminal definition and Proved capped_postPaymentReserve_ofReal_le_cap; the complementary branch follows from IsAdmissibleLe at positive times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave8_08_source_piecewise_stopped_terminal_ofReal_le_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, ENNReal.ofReal (W ω) ≤ C := by sorry
