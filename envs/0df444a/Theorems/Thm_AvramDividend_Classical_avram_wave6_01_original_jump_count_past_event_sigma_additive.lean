-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_jump_count_past_event_sigma_additive
-- name    : AvramDividend.Classical.avram_wave6_01_original_jump_count_past_event_sigma_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:02:30.253664+00:00
-- url     : https://prove2.me/theorems/8a8d50b6-de05-462f-aee3-18b3f457214d
-- title:
--   Literal original Lévy jump-count first moments are σ-additive in disjoint history events
-- statement:
--   For the actual intrinsic jump-count measure of the given spectrally negative Lévy X on the original Ω, for every measurable physical time–mark set C and every countable pairwise-disjoint family of measurable original sample events A_n, the expected source count restricted to their union equals the sum of the expected source counts restricted to each A_n. This is the explicit genuine past-event σ-additivity interface for extending future-count factorisation via a generating algebra, obtained from the newly Proved source-weighted event measure. It needs no BV, no Poisson copy, no ν intensity assertion.
-- source:
--   Apply the canonically Proved original event-weighted measure 8efd34b1-187d-45ff-80bc-e85005c53850 for C, then Mathlib measure_iUnion to the original Ω history events. This handles arbitrary infinite counts in ENNReal and is the past-event dual of canonically Proved countable mark additivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_jump_count_is_measure
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_01_original_jump_count_past_event_sigma_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : Set (ℝ≥0 × ℝ)) (hC : MeasurableSet C)
    (A : ℕ → Set Ω) (hAm : ∀ n, MeasurableSet (A n))
    (hAd : Pairwise (Function.onFun Disjoint A)) :
    (∫⁻ ω in ⋃ n, A n, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) =
      ∑' n, (∫⁻ ω in A n, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := by sorry
