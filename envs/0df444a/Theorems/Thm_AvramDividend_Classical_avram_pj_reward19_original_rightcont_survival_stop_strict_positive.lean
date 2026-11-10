-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward19_original_rightcont_survival_stop_strict_positive
-- name    : AvramDividend.Classical.avram_pj_reward19_original_rightcont_survival_stop_strict_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:33:24.808232+00:00
-- url     : https://prove2.me/theorems/fffc9a01-c920-46ad-b5d1-bf7dc939b17a
-- title:
--   Genuine unbounded-variation controlled reserve is strictly positive at a right-continuous stopping clock before ruin
-- statement:
--   Exact original controlled-path survival lower-bound at any finite right-continuous stopping clock, without a separately passed event-measurability hypothesis. Under an admissible strategy and unbounded variation, the reserve at a pre-ruin stopped clock is strictly positive almost surely. This is a prerequisite for the positive-reserve floor exhaustion in the original pure-jump stopped reward theorem 8d851948, not a replacement for the stopped Ito source and dividend ledger.
-- source:
--   Direct original-filtration instantiation of authoritative Proved 9cc18bac with the stopping-event measurability obtained from the actual IsStoppingTime hypothesis and original IsAdmissibleLe strategy field.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_controlled_rightcont_finite_stopping_strict_positive
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward19_original_rightcont_survival_stop_strict_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, (ρ ω : ℝ≥0∞) < ruinTime X x D ω →
      0 < riskProcess X x D (ρ ω) ω := by sorry
