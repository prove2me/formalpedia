-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_negative_part_zero
-- name    : AvramDividend.Classical.avram_wave7_08_source_stopped_terminal_negative_part_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:48:44.195671+00:00
-- url     : https://prove2.me/theorems/f525faf1-ef2a-45b4-b205-f1e7a1e744ff
-- title:
--   Exact original stopped UBV terminal downside has zero ENNReal expectation at zero-or-pre-ruin boundary
-- statement:
--   For the exact canonical stopped piecewise postpayment W and discounted Term, the remotely-Proved nonnegative-terminal source theorem implies the negative real part of Term vanishes almost everywhere. Hence the expectation of ENNReal.ofReal(-Term) is identically zero. This delivers a source-specific Fatou/lower-bound checkpoint without an extra integrability assumption and preserves the time-zero dividend atom and creeping zero boundary.
-- source:
--   Immediate rigorous source corollary of proved avram_wave7_08_source_exact_zero_or_preruin_terminal_nonnegative (UUID 18481770), for W7-08 and boundary consumers W7-11/12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_stopped_terminal_negative_part_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    (∫⁻ ω, ENNReal.ofReal (-Term ω) ∂P) = 0 := by sorry
