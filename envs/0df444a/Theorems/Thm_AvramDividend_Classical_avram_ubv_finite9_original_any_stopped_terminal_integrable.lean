-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_any_stopped_terminal_integrable
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_any_stopped_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:06:31.368741+00:00
-- url     : https://prove2.me/theorems/ec593f32-19d1-4d88-94a9-80feadfe9005
-- title:
--   Finite-cap integrability of original discounted terminal at any stopped clock
-- statement:
--   For every nonnegative stopped clock and original right-payment/ruin reserve, finite cap uniformly bounds the discounted terminal value. If the actual source terminal term is almost-everywhere strongly measurable then it is integrable, without the stochastic Itô identity or special integer horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_any_stopped_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ ω) ω - rightLimit D (σ ω) ω
      else riskProcess X x D (σ ω) ω)
    (q : ℝ) (hq : 0 ≤ q)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (σ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P) :
    Integrable Term P := by sorry
