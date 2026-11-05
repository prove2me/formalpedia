-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
-- name    : AvramDividend.Classical.avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:04:23.066353+00:00
-- url     : https://prove2.me/theorems/10c9f283-cf42-461c-bd4d-1f626bff2e5c
-- title:
--   Actual original bounded-random-clock signed postpayment HJB terminal is L1 without positive-part clipping
-- statement:
--   For the original BV spectrally negative Levy source, any measurable observation clock bounded by a deterministic finite H yields an integrable true strict-survival discounted post-rightpayment terminal w(U_after). The statement is the actual signed term with no max(0,.) wrapper. It preserves the exact physical reserve, time-zero and terminal rightLimit convention, positive cap with contact, and strict ruin exclusion.
-- source:
--   Two Proved/public exact source theorems: 8949220f BV bounded measurable random-clock clipped terminal L1, and 331f6956 any-clock strict-survival positive-part equality to the signed source terminal. No Open P3 or E2 theorem import.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_measurable_random_clock_survival_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_any_clock_strict_survival_terminal_max_eq_signed

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0) P := by sorry
