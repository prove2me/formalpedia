-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_all_caps_chronological_stopped_terminal_nonnegative
-- name    : AvramDividend.Classical.avram_wave5_03_original_all_caps_chronological_stopped_terminal_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:16:02.588796+00:00
-- url     : https://prove2.me/theorems/51e62fce-6d4a-4c13-b2ff-c887fd685d6e
-- title:
--   Both canonical BV and corrected UBV original chronological stopped terminal payoff nonnegative for ALL caps including zero
-- statement:
--   On the actual original spectrally negative Lévy controlled reserve and θ=toNNReal(min(T,ruinTime)), select postpayment at θ=0 or surviving T<ruin, and prepayment book reserve at positive ruin. Under precisely the separate BV C1/UBV C2 smoothness alternative, 0≤w0, negative-side extension, gradient and genuine admissible cap, prove w(Wθ)≥0 for EVERY C≥0, including C=0 not excluded by corrected UBV canonical. Split C=0 and use source-specific zero-cap actual chronological terminal theorem, or 0<C and the already Proved original full-cap terminal theorem f72f93f3. Never assume globally w≥0 and preserve the ruin-causing book reserve.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i), same-path terminal sign for both BV ef7e6c20 and corrected UBV 429e17ca; imports Proved f72f93f3 positive-cap and new source zero-cap terminal theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_chronological_stopped_terminal_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_zero_cap_chronological_stopped_terminal_nonnegative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_all_caps_chronological_stopped_terminal_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0) :
    let τ : ℝ≥0∞ := ruinTime X x D ω
    let θ : ℝ≥0 := (min (T : ℝ≥0∞) τ).toNNReal
    let W : ℝ :=
      if θ = 0 ∨ (T : ℝ≥0∞) < τ then
        x + X.X θ ω - rightLimit D θ ω
      else riskProcess X x D θ ω
    0 ≤ w W := by sorry
