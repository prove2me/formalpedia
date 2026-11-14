-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b207_original_canonical_bounded_marked_grid_measurable_integrable_real_dom
-- name    : AvramDividend.Classical.avram_b207_original_canonical_bounded_marked_grid_measurable_integrable_real_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:55:26.291092+00:00
-- url     : https://prove2.me/theorems/7b6ec639-3dd3-4d6c-9239-085c18bb050c
-- title:
--   Canonical genuine original physical random-grid marked-cell cardinal is measurable integrable and dominated by real Poisson source count
-- statement:
--   For any finite monotone random physical grid of the original spectrally negative Levy source with measurable endpoints and bounded horizon under finite negative-mark intensity, the genuine jump-containing cell count is a measurable and integrable real random variable and is dominated almost everywhere by the actual full negative source Poisson count. B198 supplies full original source count measurability, B205 establishes the genuine marked-cell measurability and conull real count bound, and B140 establishes its integrability directly using the original intensity. Thus all count-related premises needed by original stopped Ito mixed mesh energy are provided without extra source-count measurability or exceptional infinite-count assumptions.
-- source:
--   Proved B198, B205, B140 on original Levy source, random physical monotone mesh, finite negative activity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b205_original_canonical_grid_marked_count_measurable_and_real_poisson_dom
import Theorems.Thm_AvramDividend_Classical_avram_b140_original_ae_selected_negative_jump_cells_uniform_count_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b207_original_canonical_bounded_marked_grid_measurable_integrable_real_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (T : ℝ≥0) (hT : T ≤ (n : ℝ≥0))
    (S : Finset ℕ)
    (grid : Ω → ℕ → ℝ≥0)
    (hMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (hHorizon : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ T)
 :
    let J : Ω → Finset ℕ := fun ω => by
      classical
      exact S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) ∧
    Integrable (fun ω => ((J ω).card : ℝ)) P ∧
    (∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal) := by sorry
