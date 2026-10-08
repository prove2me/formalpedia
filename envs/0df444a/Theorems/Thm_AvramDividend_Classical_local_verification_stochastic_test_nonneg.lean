-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_test_nonneg
-- name    : AvramDividend.Classical.local_verification_stochastic_test_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:20:15.096489+00:00
-- url     : https://prove2.me/theorems/740c5427-ee17-4cbd-a18d-6117c9222883
-- title:
--   Local-verification HJB assumptions imply exactly the terminal nonnegativity hypothesis of both BV and UBV truncated stochastic lemmas
-- statement:
--   For any capped admissible strategy with 0≤x≤C, the original HJB and w(0)≥0 hypotheses ensure w(U_t)≥0 for every positive time before ruin. The controlled reserve U_t is nonnegative by the proven ruin-time lemma and remains under cap C by capped admissibility. The newly derived HJB gradient bound ensures w is nonnegative on that reserve interval. This discharges the otherwise unproved extra hw_nonneg premise appearing identically in both BV and UBV stochastic verification leaves.
-- source:
--   Children riskProcess_nonneg_before_ruin, admissibleLe_riskProcess_le_cap_all_times, and local_verification_w_nonneg_below_cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_stochastic_test_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by sorry
