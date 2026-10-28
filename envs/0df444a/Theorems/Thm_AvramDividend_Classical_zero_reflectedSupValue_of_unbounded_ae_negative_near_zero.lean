-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_ae_negative_near_zero
-- name    : AvramDividend.Classical.zero_reflectedSupValue_of_unbounded_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:39:21.178768+00:00
-- url     : https://prove2.me/theorems/ec1ef190-efed-4b57-80a4-dd9b7bb5abbe
-- title:
--   Unbounded zero-barrier scale identity from almost-sure negative near-zero paths
-- statement:
--   In the unbounded-variation branch the zero-barrier reflected dividend identity follows from almost-sure regularity of the negative half-line at time zero. The already Proved pathwise bridge converts negative excursions to immediate reflected ruin, and the zero reflected value theorem supplies equality with the analytic scale-function candidate. This is a conditional exact version of open root-connected zero_reflectedSupValue_eq_barrierValue.
-- source:
--   Direct conditional branch of b83a725b-f7cf-4aef-8105-310d38d8cd46, using two canonically Proved prerequisites.

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_of_unbounded_instant_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_reflectedSupValue_of_unbounded_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by sorry
