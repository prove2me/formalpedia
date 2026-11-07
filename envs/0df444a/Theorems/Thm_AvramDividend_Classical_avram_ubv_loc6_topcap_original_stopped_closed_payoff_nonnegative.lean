-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_topcap_original_stopped_closed_payoff_nonnegative
-- name    : AvramDividend.Classical.avram_ubv_loc6_topcap_original_stopped_closed_payoff_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:40:54.929776+00:00
-- url     : https://prove2.me/theorems/4fb1747b-2d17-419c-a92a-1e6758b1dab5
-- title:
--   Original UBV infinite-cap natural-clock terminal and Iic Stieltjes cash are nonnegative for all paths
-- statement:
--   Under the original top-cap HJB candidate hypotheses, the exact exponential-discounted terminal w of the original stopped reserve/right-limit convention plus dividendMeasure cash over paymentTimes intersect Iic tau is nonnegative for every sample path, including time-zero, ruin overshoot and horizon atoms. This is a source-exact independent non-negativity component, with no extra growth, martingale or integrability assumption.
-- source:
--   UBV-LOC6 original stopped payoff sign bridge for fa7052b1. Publication revision v2 after previous dependency-order failure; required top-cap global sign helper 8e855eb9 was verified Proved before this publication attempt.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_infinitecap_candidate_globally_nonnegative

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_loc6_topcap_original_stopped_closed_payoff_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCtop : C = ⊤) :
    ∀ ω, 0 ≤ Term ω + Cash ω := by sorry
