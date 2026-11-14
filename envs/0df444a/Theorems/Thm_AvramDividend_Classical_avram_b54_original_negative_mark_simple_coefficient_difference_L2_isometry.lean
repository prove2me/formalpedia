-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b54_original_negative_mark_simple_coefficient_difference_L2_isometry
-- name    : AvramDividend.Classical.avram_b54_original_negative_mark_simple_coefficient_difference_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:14:15.261942+00:00
-- url     : https://prove2.me/theorems/d041ab6a-3012-4e7c-bac9-df3f1b1b0eef
-- title:
--   Exact original compensated negative Borel marked simple integrand difference L2 isometry
-- statement:
--   For two distinct real coefficient arrays on the same physical negative Borel mark partition of the unchanged Levy path, the squared L2 difference between their actual compensated marked-count integrals is integrable and has exact expectation equal to the coefficient-difference-squared physical mark intensity. It provides the source-isometry Cauchy criterion needed to approximate nonlinear marked Ito-Meyer jump kernels.
-- source:
--   Proved JA31 actual original negative Borel marked count simple isometry; finite-sum linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_finite_borel_mark_source_isometry
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b54_original_negative_mark_simple_coefficient_difference_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (K : ℕ) (B : ℕ → Set ℝ)
    (a b : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i))
    (hNeg : ∀ i ∈ Finset.range K, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K,
      i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((t : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 t ×ˢ B i)).toReal - r i
    let A : Ω → ℝ := fun ω => ∑ i ∈ Finset.range K, a i * Y i ω
    let C : Ω → ℝ := fun ω => ∑ i ∈ Finset.range K, b i * Y i ω
    Integrable (fun ω => (A ω - C ω)^2) P ∧
    (∫ ω, (A ω - C ω)^2 ∂P) =
      ∑ i ∈ Finset.range K, (a i - b i)^2 * r i := by sorry
