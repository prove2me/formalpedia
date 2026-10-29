-- Prove2me | Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
-- name    : AvramDividend.Classical.ae_negative_near_zero_of_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:20:47.874263+00:00
-- url     : https://prove2.me/theorems/703dc740-a8df-4cd1-9ff1-622fd81d68c7
-- title:
--   Unbounded variation implies almost-sure negative values arbitrarily close to zero
-- statement:
--   A spectrally negative Levy process of unbounded variation visits strictly negative values at arbitrarily small positive times, almost surely. This is the almost-sure path regularity (zero is regular for the negative half-line) that feeds the instantaneous down-exit clock used by the zero-start stopped-scale identity and the unbounded-variation leg of the two-sided exit balance.
-- source:
--   Parent AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity (aed50a34): its repair attempt 15378 fabricated this premise (hDown0 via misapplied hnbv) and failed on 5 independent CE groups. Proved converter chat04_down_exit_time_zero_of_negative_near_zero (ac9a5651) turns per-path near-zero negativity into a zero down-exit clock; Proved zero-start lemma chat04_unbounded_zero_start_stopped_scale_of_down_exit_zero (8029c619) consumes the a.e. clock. No authoritative theorem concludes the a.e. near-zero negativity itself (catalogue searches return only consumers).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ae_negative_near_zero_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 := by sorry
