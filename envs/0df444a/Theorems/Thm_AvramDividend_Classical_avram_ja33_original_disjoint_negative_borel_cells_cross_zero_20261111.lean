-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja33_original_disjoint_negative_borel_cells_cross_zero_20261111
-- name    : AvramDividend.Classical.avram_ja33_original_disjoint_negative_borel_cells_cross_zero_20261111
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T22:11:40.600555+00:00
-- url     : https://prove2.me/theorems/d2705069-242f-4cb5-a302-c937297aaa1a
-- title:
--   Disjoint arbitrary negative Borel jump-mark cells have exact original centred covariance zero
-- statement:
--   On the actual finite-activity original Lévy process, disjoint measurable negative jump mark cells have integrable centred count cross-product with zero expectation. This is the physical off-diagonal input needed for arbitrary finite Borel-mark simple isometry.
-- source:
--   True-source physical Poisson random measure moment bridge for JA30 finite Borel partition. Different from harmonic-annulus-only moments; needs within-annulus Borel control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja33_original_disjoint_negative_borel_cells_cross_zero_20261111
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hNegA : A ⊆ Iio (0 : ℝ)) (hNegB : B ⊆ Iio (0 : ℝ))
    (hDisj : Disjoint A B) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let rA : ℝ := ((T : ℝ≥0∞) * X.ν A).toReal
    let rB : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    let YA : Ω → ℝ := fun ω =>
      (NX ω (Ioc 0 T ×ˢ A)).toReal - rA
    let YB : Ω → ℝ := fun ω =>
      (NX ω (Ioc 0 T ×ˢ B)).toReal - rB
    Integrable (fun ω => YA ω * YB ω) P ∧
      (∫ ω, YA ω * YB ω ∂P) = 0 := by sorry
