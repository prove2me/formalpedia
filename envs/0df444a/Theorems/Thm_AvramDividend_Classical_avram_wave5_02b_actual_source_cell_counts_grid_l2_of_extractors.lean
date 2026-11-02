-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_cell_counts_grid_l2_of_extractors
-- name    : AvramDividend.Classical.avram_wave5_02b_actual_source_cell_counts_grid_l2_of_extractors
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:34:19.707751+00:00
-- url     : https://prove2.me/theorems/c9733018-5e8f-4080-8323-c802bf9424c3
-- title:
--   Original Lévy marked-cell count finite-grid L² identity from future extractors
-- statement:
--   For the original Lévy source, intrinsic jump measure and actual marked cell counts, the square of a predictable finite grid sum of centred counts has its Poisson variance sum. The past independence needed for the grid identity follows from a measurable shifted-source-path count extractor. Existence of the extractor and the Poisson count law remain explicit hypotheses. The statement requires no infinite sequence of auxiliary marks or enlargement of the original sample space.
-- source:
--   Original future-path extractor independence 86ab54a5-0f9f-4e69-a76c-19f22db4d908 and Proved count grid isometry 393e1554-ed58-4330-9e12-2328c6ad09ff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_grid_poisson_l2_isometry_natural

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem AvramDividend.Classical.avram_wave5_02b_actual_source_cell_counts_grid_l2_of_extractors
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
    (grid : ℕ → ℝ≥0) (C : ℕ → Set ℝ)
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (Fpath : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hFpath : ∀ i, Measurable (Fpath i))
    (hRep : ∀ i ω, Fpath i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) = K i ω)
    (hKsource : ∀ i ω, (K i ω : ℝ≥0∞) =
      NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hH : ∀ i, Measurable[𝓕 (grid i)] (H i))
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable
      (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
    (hPrefixPast : ∀ i, Measurable[𝓕 (grid i)] (fun ω =>
      ∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))))
    (n : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range n, H i ω *
        ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
          (r i : ℝ))) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
        (r i : ℝ))) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, (r i : ℝ) * ∫ ω, (H i ω) ^ 2 ∂P := by sorry
