-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1_from_source
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1_from_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:07:35.381956+00:00
-- url     : https://prove2.me/theorems/533559a4-7e66-4e55-b891-e89b76884025
-- title:
--   Original BV right-horizon canonical stopped postpayment terminal L1 from record fields, no extra conditions
-- statement:
--   The canonical source SpectrallyNegativeLevy record itself supplies X.X_zero identically and X.isProbability. Therefore the proved original BV right-postpayment terminal L1 holds at every fixed deterministic S, for finite or infinite cap, using only the exact canonical BV admissibility, C1/gradient and hJump assumptions. Source positivity and measurability are discharged by the imported proved P3-G L1 helper.
-- source:
--   SpectrallyNegativeLevy.X_zero and .isProbability actual source fields; P3-G original BV strict postpayment terminal L1; all canonical signed P3 assumptions.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1_from_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (S : ℝ≥0) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) P := by sorry
