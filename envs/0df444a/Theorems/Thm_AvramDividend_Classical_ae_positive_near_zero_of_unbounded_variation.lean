-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_positive_near_zero_of_unbounded_variation
-- name    : AvramDividend.Classical.ae_positive_near_zero_of_unbounded_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-26T08:15:58.698645+00:00
-- url     : https://prove2.me/theorems/be25ce06-ecbc-4482-829b-bcd40163d088
-- title:
--   Unbounded variation implies almost-sure positive values arbitrarily close to zero
-- statement:
--   A spectrally negative Levy process of unbounded variation visits strictly positive values at arbitrarily small positive times, almost surely. This is the almost-sure path regularity (zero is regular for the positive half-line) that feeds the a.e. upward-regularity premise hplus of the proved upper-endpoint stopped-scale identity and hence the unbounded-variation leg of the two-sided exit balance.
-- source:
--   Parent AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity (aed50a34): unbounded leg of the stopped-scale identity 09663d0d feeding 3e1ce2c8, 5bcf90e1 and barrier_strategy_value. Proved upper-endpoint lemma chat04_upper_endpoint_stopped_scale_of_ae_upward_regularity (ecb37154) consumes an a.e. upward-regularity premise hplus of exactly this shape; Proved zero-start lemma 8029c619 consumes the mirrored downward premise via Proved converter ac9a5651 and Open ae_negative_near_zero (703dc740). No authoritative theorem concludes the a.e. near-zero positivity itself (catalogue search for upward regularity returns only the zero-start consumer). Mirror of the accepted problem 703dc740 with the inequality side flipped.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_positive_near_zero_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω := by sorry
