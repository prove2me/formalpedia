-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_actual_piecewise_discounted_terminal_auto_measurable
-- name    : AvramDividend.Classical.avram_wave6_06_original_actual_piecewise_discounted_terminal_auto_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:32:51.936494+00:00
-- url     : https://prove2.me/theorems/675648d7-9de7-491d-a31a-2fe54a9b52ee
-- title:
--   Actual original ruin-stopped discounted HJB terminal is automatically measurable
-- statement:
--   Under the genuine original admissible dividend strategy and original right-continuous stopping time, show a.e. strong measurability of the exact discounted Avram piecewise terminal w(W), where W is post-right-payment at zero/pre-ruin and book value at positive ruin, w is continuous on [0,∞) and zero on negatives. Compose independently Proved exact W meas, original w Borel meas and original clock real meas. No stochastic Ito identity or extra terminal-meas assumption.
-- source:
--   Avram Proposition 4(i), Eq (5.11)-(5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_actual_piecewise_discounted_terminal_auto_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    AEStronglyMeasurable Term P := by sorry
