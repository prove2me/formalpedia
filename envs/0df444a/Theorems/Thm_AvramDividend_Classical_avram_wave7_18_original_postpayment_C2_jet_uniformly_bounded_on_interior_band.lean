-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
-- name    : AvramDividend.Classical.avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:57:39.632012+00:00
-- url     : https://prove2.me/theorems/13967844-4e8f-48b6-82ca-9878ac280d47
-- title:
--   Uniform bounds for C² value, gradient and Hessian on original post-payment reserve interior band
-- statement:
--   For the original spectrally negative Lévy reserve with admissible dividend strategy and post-payment reserve Z_t=x+X.X t-rightLimit D t, a positive finite compact state band [a,b] with its upper endpoint strictly below the source cap C is contained in the exact C² domain of w. Consequently one finite deterministic real bound M controls the absolute value of w, its ordinary first derivative, and its ordinary second derivative at Z_t, for every original sample path and time whenever Z_t lies in the band. This also covers C=∞ and does not claim integrability without a stopped finite-mass martingale or compensator measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_postpayment_C2_jet_uniformly_bounded_on_interior_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (ω : Ω) (t : ℝ≥0),
        x + X.X t ω - rightLimit D t ω ∈ Set.Icc a b →
        |w (x + X.X t ω - rightLimit D t ω)| ≤ M ∧
        |deriv w (x + X.X t ω - rightLimit D t ω)| ≤ M ∧
        |deriv (deriv w) (x + X.X t ω - rightLimit D t ω)| ≤ M := by sorry
