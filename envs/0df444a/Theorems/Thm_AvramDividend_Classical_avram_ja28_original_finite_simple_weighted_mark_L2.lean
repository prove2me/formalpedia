-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja28_original_finite_simple_weighted_mark_L2
-- name    : AvramDividend.Classical.avram_ja28_original_finite_simple_weighted_mark_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T18:18:59.044097+00:00
-- url     : https://prove2.me/theorems/d29b7a18-d6d2-45b4-916b-35b4e8ca5d9f
-- title:
--   Exact original finite-simple negative Borel marked-jump compensated L2 variance
-- statement:
--   For finitely many pairwise disjoint negative Borel mark sets, the original Levy source centred physical jump counts are pairwise orthogonal, and a finite real weighted sum has exact second moment equal to the sum of squared weights times the genuine original Tν(B) source intensities.
-- source:
--   Direct consequence of Proved f0a48623 partition centred exact variances and off-diagonal zero covariance, and Proved 7e6df6ff finite orthogonal-sum L2 isometry. This finite-simple case is the algebraic core of still-open 4106f6a7 bounded measurable mark raw moments and 2a4be8dd compensated marked-strip isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja30_original_negative_borel_partition_count_moments
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_finite_pairwise_orthogonal_real_L2_isometry
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja28_original_finite_simple_weighted_mark_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (k : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range k, MeasurableSet (B i))
    (hNeg : ∀ i ∈ Finset.range k, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k,
      i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let A : ℕ → Ω → ℝ := fun i ω =>
      c i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    (∫ ω, (∑ i ∈ Finset.range k, A i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range k, (c i) ^ 2 * r i := by sorry
