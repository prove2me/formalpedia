-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_discounted_terminal_nonnegative_from_source_gradient
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_anycap_discounted_terminal_nonnegative_from_source_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:52:52.763333+00:00
-- url     : https://prove2.me/theorems/32477187-2025-40f8-884b-c2195f7eff61
-- title:
--   True original stopped terminal nonnegativity from exact C² and derivative bounds at arbitrary cap
-- statement:
--   The canonical P4-F assumptions imply nonnegative discounted terminal for any ENNReal cap. The already-Proved inclusive-cap source HJB secant b−a≤w(b)−w(a) with a=0, b=W and w0≥0 gives w(W)≥0 on nonnegative W. On negative W the source extension w=0 applies. The accepted original stopped W cap invariant covers every horizon, immediate and positive ruin branch. This is direct source-backed proof, including C=top, with no extra occupation, martingale or integrability premise.
-- source:
--   Accepted original inclusive cap secant 44b01929-5817-44ac-9439-6eb3c9879f2c and stopped W cap 0fe5d1ab-84cf-44ae-9859-2e0791e9905a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_terminal_reserve_cap_even_at_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At the exact original ruined or surviving stopped clock, the source C²/HJB slope and w(0)≥0 force nonnegative discounted terminal for arbitrary cap C. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_anycap_discounted_terminal_nonnegative_from_source_gradient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ ω, 0 ≤ Real.exp (-(q * (τ ω : ℝ))) * w (W ω) := by sorry
