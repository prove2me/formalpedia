-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_masked_contact_tail_intersection_eq_endpoint
-- name    : AvramDividend.Classical.avram_p3_grid4_original_masked_contact_tail_intersection_eq_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:04:34.817387+00:00
-- url     : https://prove2.me/theorems/30a7c0a1-d3c1-42bf-8255-3abfdebe6887
-- title:
--   Actual stopped shrinking contact tails intersect in precisely the payment-masked endpoint
-- statement:
--   For the exact original X,D and paymentTimes(ruinTime X x D ω), shrinking positive-width half-open contact tails (tau-delta_n,tau] with delta_n→0 have common intersection exactly paymentTimes ∩ {tau}. This preserves the surviving horizon right-payment singleton but excludes a positive ruin singleton. It is the exact set identity needed to pass finite original discounted tail mass through measure-continuity-from-above, without making any assumption about dividend atoms or a surrogate process.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_masked_contact_tail_intersection_eq_endpoint
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (τ : ℝ≥0)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    (⋂ n : ℕ, paymentTimes (ruinTime X x D ω) ∩
      Ioc ((τ : ℝ) - δ n) (τ : ℝ)) =
        paymentTimes (ruinTime X x D ω) ∩ ({(τ : ℝ)} : Set ℝ) := by sorry
