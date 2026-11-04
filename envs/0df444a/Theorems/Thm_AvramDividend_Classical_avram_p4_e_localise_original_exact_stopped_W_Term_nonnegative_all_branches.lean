-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:17:25.189278+00:00
-- url     : https://prove2.me/theorems/f6fef241-4795-4ee7-bb8b-1b7732588e23
-- title:
--   Canonical original stopped UBV terminal is nonnegative at zero, survival and positive ruin without overshoot sign
-- statement:
--   At the exact original P4-F piecewise stopped state W, choose the post-right-payment reserve at τ=0 or strictly before ruin, and the source book riskProcess at positive ruin. For every sample path, under corrected w(0)≥0, zero extension for negatives, C2/HJB gradient bound on the strictly interior and original cap admissibility, the discounted terminal Term is nonnegative for any q. Uses independently Proved all-cap actual postpayment verification-value nonnegativity and original at-any-time book reserve nonnegativity (with the BV alternative discharged by hBV). Does not assume riskProcess at ruin≤0: right-dividend control is left-continuous, and ruin can occur at a right-payment boundary. No stochastic Ito identity is asserted.
-- source:
--   Proved genuine source 06839544 allcap UBV postpayment, 52dd2155 original book reserve terminal, exact canonical P4-F W convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_allcap_postpayment_terminal_candidate_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_book_reserve_terminal_nonnegative_separate_gradient
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, 0 ≤ Term ω := by sorry
