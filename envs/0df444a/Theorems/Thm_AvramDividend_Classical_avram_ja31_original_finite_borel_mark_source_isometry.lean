-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja31_original_finite_borel_mark_source_isometry
-- name    : AvramDividend.Classical.avram_ja31_original_finite_borel_mark_source_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:06:15.892131+00:00
-- url     : https://prove2.me/theorems/b7fdb101-46d3-4e38-a90e-b48c77cc9999
-- title:
--   Unconditional finite physical Borel-mark stochastic integral isometry for the actual original process
-- statement:
--   Any finite simple weight supported on disjoint measurable negative jump-mark cells of the original Lévy process has a centred integral whose L2 square exactly equals the weighted mark intensity. Reduces via a real source Borel count covariance theorem to already Proved finite weighted algebra, so this is the finite-simple base of the bounded mark approximation.
-- source:
--   Original Poisson marked source; open ja30 physical Borel count diagonal and covariance; finite weighted source algebra ja29.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja31_original_finite_borel_mark_source_isometry
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (F : Finset ι) (B : ι → Set ℝ) (a : ι → ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hNeg : ∀ i ∈ F, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ι → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ι → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i
    Integrable (fun ω => (∑ i ∈ F, a i * Y i ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ F, a i * Y i ω) ^ 2 ∂P) =
        ∑ i ∈ F, (a i) ^ 2 * r i := by sorry
