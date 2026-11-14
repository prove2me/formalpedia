-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_finite_signed_disjoint_negative_borel_cells_cross_zero_20261113
-- name    : AvramDividend.Classical.avram_a21_original_finite_signed_disjoint_negative_borel_cells_cross_zero_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:49:23.812924+00:00
-- url     : https://prove2.me/theorems/84a35d10-3d56-4b35-a3d7-32b835a509f4
-- title:
--   Finite signed Borel-mark simple compensated fields have zero cross covariance for disjoint supports
-- statement:
--   On the ORIGINAL Levy probability space, finite signed simple compensated negative marked-jump fields, each built as a finite real-weighted sum of actual original marked Poisson counts minus exact intensity, have an integrable product and zero expected product if every mark cell in the first field is disjoint from every mark cell in the second field. This extends the earlier Proved pairwise Borel-cell covariance via bilinearity and finite Bochner sums and supplies the finite-simple step for Gaussian/omitted negative mark orthogonality.
-- source:
--   Direct algebra of finite signed simple original marked Poisson source fields, using pending weighted disjoint-cell covariance helper 8959ee69 and pinned Mathlib integrable_finsetSum / integral_finsetSum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_weighted_disjoint_negative_borel_counts_cross_zero_20261113
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_finite_signed_disjoint_negative_borel_cells_cross_zero_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι) (G : Finset κ)
    (A : ι → Set ℝ) (B : κ → Set ℝ)
    (a : ι → ℝ) (b : κ → ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hB : ∀ j ∈ G, MeasurableSet (B j))
    (hNegA : ∀ i ∈ F, A i ⊆ Iio (0 : ℝ))
    (hNegB : ∀ j ∈ G, B j ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ F, ∀ j ∈ G, Disjoint (A i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let YA : ι → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 T ×ˢ A i)).toReal -
        ((T : ℝ≥0∞) * X.ν (A i)).toReal
    let YB : κ → Ω → ℝ := fun j ω =>
      (NX ω (Ioc 0 T ×ˢ B j)).toReal -
        ((T : ℝ≥0∞) * X.ν (B j)).toReal
    Integrable (fun ω => (∑ i ∈ F, a i * YA i ω) *
      (∑ j ∈ G, b j * YB j ω)) P ∧
      (∫ ω, (∑ i ∈ F, a i * YA i ω) *
        (∑ j ∈ G, b j * YB j ω) ∂P) = 0 := by sorry
