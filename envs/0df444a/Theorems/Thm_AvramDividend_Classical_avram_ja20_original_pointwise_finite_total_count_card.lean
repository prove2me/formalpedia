-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja20_original_pointwise_finite_total_count_card
-- name    : AvramDividend.Classical.avram_ja20_original_pointwise_finite_total_count_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:12:58.353895+00:00
-- url     : https://prove2.me/theorems/53e64bd6-88a3-4e3f-a142-3e61ad05fcc4
-- title:
--   Pointwise original finite marked-time cardinality bound under finite total negative count
-- statement:
--   At a fixed original sample path ω, if the total negative jump counting measure up to T is finite, the finite set of cutoff-negative jump times has cardinality bounded by that original total count. This removes reliance on an a.e. statement when proving the historical pointwise compensated smallband bound.
-- source:
--   J-A20 split from a3c3f9c8 direct 112-line attempt blocked by code-budget gate; derives from Proved wave7_06 marked-time finite/cardinality equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja20_original_pointwise_finite_total_count_card
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) (T : ℝ≥0) (ω : Ω)
    (hNfin :
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) < ⊤) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔
         0 < u ∧ u ≤ T ∧
         -1 < X.X u ω -
           Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∧
         X.X u ω -
           Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
           -(1 / ((k : ℝ) + 1))) ∧
      (F.card : ℝ) ≤
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal := by sorry
