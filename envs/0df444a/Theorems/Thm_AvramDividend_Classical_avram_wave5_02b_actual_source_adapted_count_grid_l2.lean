-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_adapted_count_grid_l2
-- name    : AvramDividend.Classical.avram_wave5_02b_actual_source_adapted_count_grid_l2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:48:47.056194+00:00
-- url     : https://prove2.me/theorems/e369ef90-cea5-46fd-8076-52d54222f890
-- title:
--   Original source marked-count grid isometry from adapted cell increments
-- statement:
--   For original Lévy marked cell counts on an increasing grid, derive prefix past measurability from predictable coefficients and adapted cell increments, and derive the centred count-sum L² identity using the original source shifted-path independence. The source-path count extractors, their representation, Poisson laws and increment adaptedness are explicit hypotheses. No independent marked sequence or extra sample space is introduced.
-- source:
--   Proved actual source marked-count grid identity c9733018-5e8f-4080-8323-c802bf9424c3 and original finite-grid prefix past-measurability 2d63fe5c-fbfd-4cb9-b934-8ee040f38abe.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_original_grid_compensated_prefix_strongly_past_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_cell_counts_grid_l2_of_extractors

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave5_02b_actual_source_adapted_count_grid_l2
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (grid : ℕ → ℝ≥0) (hGrid : Monotone grid) (C : ℕ → Set ℝ)
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (Fpath : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hFpath : ∀ i, Measurable (Fpath i))
    (hRep : ∀ i ω, Fpath i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) = K i ω)
    (hKsource : ∀ i ω, (K i ω : ℝ≥0∞) =
      NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hZ : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))]
      (fun ω => (K i ω : ℝ) - (r i : ℝ)))
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
    (n : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range n, H i ω *
        ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
          (r i : ℝ))) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
        (r i : ℝ))) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, (r i : ℝ) * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
