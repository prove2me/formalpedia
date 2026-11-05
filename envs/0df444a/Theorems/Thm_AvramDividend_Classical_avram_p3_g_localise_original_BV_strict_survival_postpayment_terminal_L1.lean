-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:52:51.011888+00:00
-- url     : https://prove2.me/theorems/5110247e-e043-4e56-8754-c1ce815a2b98
-- title:
--   Actual original BV strict pre-ruin right-postpayment terminal is integrable at every deterministic time
-- statement:
--   For every bounded-variation original spectrally negative Levy strategy at a deterministic horizon and either finite or infinite cap, the canonical strict-survival discounted right-postpayment terminal is L1 under the standing finite-measure and zero-time source properties. The Proved strict prepayment terminal L1 dominates the postpayment payoff pointwise by the canonical hJump; source adaptedness and measurable ruin time give the missing measurable terminal composition. No uniform-in-horizon integrability or zero boundary occupation is postulated.
-- source:
--   Proved original preterminal L1 d086b85a, local_verification_candidate_borel_and_postPayment_adapted 30325a04, ruinTime_measurable bbfbecf4, P3-G original postpayment dominated helper, pinned Mathlib Integrable.mono.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0) (hfinite : IsFiniteMeasure P)
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
