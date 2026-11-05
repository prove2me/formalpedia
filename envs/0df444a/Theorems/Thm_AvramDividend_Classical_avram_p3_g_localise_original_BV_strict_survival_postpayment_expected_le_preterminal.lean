-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_survival_postpayment_expected_le_preterminal
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_survival_postpayment_expected_le_preterminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:07:24.921448+00:00
-- url     : https://prove2.me/theorems/d50ca317-05b1-42c9-82fc-a54cf835e047
-- title:
--   Original BV strict-survival expected postpayment terminal is bounded by expected prepayment terminal
-- statement:
--   At each deterministic time, compare the actual original discounted post-dividend terminal reward in the canonical signed budget with the source pre-dividend reserve expected reward. Both terms are L1 under original BV, X zero-start and finite-measure assumptions by proved Prove2Me helpers. Canonical hJump, cap regularity and dividend admissibility provide the pointwise inequality; integrate with Mathlib integral_mono. There is no claim of the full cash budget or of an infinite-horizon limit.
-- source:
--   P3-G original postpayment terminal L1, original strict preterminal L1 d086b85a, P3-G strict survival postpayment domination, pinned Mathlib integral_mono.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_survival_postpayment_terminal_nonnegative_dominated
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_BV_strict_survival_postpayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_BV_strict_survival_postpayment_expected_le_preterminal
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
    (∫ ω,
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) ∂P) ≤
    (∫ ω,
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (riskProcess X x D S ω)
      else 0) ∂P) := by sorry
