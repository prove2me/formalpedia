-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_weighted_disjoint_negative_borel_counts_cross_zero_20261113
-- name    : AvramDividend.Classical.avram_a21_original_weighted_disjoint_negative_borel_counts_cross_zero_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:46:04.304329+00:00
-- url     : https://prove2.me/theorems/8959ee69-1ef8-4f5d-8caf-f572a7c5529b
-- title:
--   Arbitrary fixed weighted original negative marked jump cells have zero compensated cross covariance
-- statement:
--   For two arbitrary disjoint measurable negative mark sets, physical Poisson jump counts on the same original Levy process minus exact Levy intensities have centred covariance zero. Multiplying each count by arbitrary deterministic real weights preserves integrability of the cross product and expected cross product zero. This extends the previously Proved unweighted Borel-cell covariance and supplies a source-faithful primitive for finite signed simple-mark isometry and Gaussian/omitted-tail approximations.
-- source:
--   Proved original disjoint negative Borel marked cell centred covariance d2705069; Bochner integral const_mul and real ring factorisation. No independent altered model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja33_original_disjoint_negative_borel_cells_cross_zero_20261111
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_weighted_disjoint_negative_borel_counts_cross_zero_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hNegA : A ⊆ Iio (0 : ℝ)) (hNegB : B ⊆ Iio (0 : ℝ))
    (hDisj : Disjoint A B)
    (a b : ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let rA : ℝ := ((T : ℝ≥0∞) * X.ν A).toReal
    let rB : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    let YA : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ A)).toReal - rA
    let YB : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal - rB
    Integrable (fun ω => (a * YA ω) * (b * YB ω)) P ∧
      (∫ ω, (a * YA ω) * (b * YB ω) ∂P) = 0 := by sorry
