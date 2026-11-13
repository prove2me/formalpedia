-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja30_original_negative_borel_partition_count_moments
-- name    : AvramDividend.Classical.avram_ja30_original_negative_borel_partition_count_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:04:53.420863+00:00
-- url     : https://prove2.me/theorems/f0a48623-eb35-4027-b1d6-e062d002e8d4
-- title:
--   Original finite-activity negative Borel mark cells have exact Poisson variance and disjoint covariance zero
-- statement:
--   For the actual spectrally negative Levy process with finite negative jump intensity, arbitrary finite disjoint measurable subsets of negative marks yield centred source counts with exact variance t nu(B), integrable cross products and zero covariance on the same underlying probability space. This is the missing true physical source certificate required to obtain finite within-annulus simple-mark isometry; standard harmonic annulus count covariance does not imply it by itself.
-- source:
--   Original marked point process and finite negative measure; existing marked count extractor  d9b9e3c2, physical count source moment proof 6e234a3f for harmonic intervals, general covariance algebra 2a3d3cef. No change of measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_ja30_original_negative_borel_partition_count_moments
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (F : Finset ι) (B : ι → Set ℝ)
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
    (∀ i ∈ F, Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i) ∧
    (∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Integrable (fun ω => Y i ω * Y j ω) P ∧
      (∫ ω, Y i ω * Y j ω ∂P) = 0) := by sorry
