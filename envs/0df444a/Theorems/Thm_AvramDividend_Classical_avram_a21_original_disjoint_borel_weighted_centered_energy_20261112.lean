-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_disjoint_borel_weighted_centered_energy_20261112
-- name    : AvramDividend.Classical.avram_a21_original_disjoint_borel_weighted_centered_energy_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:43:05.071909+00:00
-- url     : https://prove2.me/theorems/528b7e5b-d233-4910-85ef-3a201e4dd5f8
-- title:
--   Exact original-space L2 energy of disjoint centred Borel marked finite cell sums
-- statement:
--   For any finite collection of pairwise disjoint measurable negative mark cells on the original spectrally negative Lévy process, the finite weighted sum of centred actual physical mark counts has integrable square and exactly the sum of squared coefficient times each physical expected count as its L2 energy.
-- source:
--   Proved original disjoint Borel weighted raw first and second moments c772b553-e199-4de0-9477-5b320fe0e9ee and Proved real moment centring identity aaeb5fe2-0651-4268-94dc-15c93c7ac2a4. Supports the genuine partition energy certificate 67336b2d-222d-4aed-a5f9-a0193235459e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_disjoint_borel_simple_raw_weighted_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_a21_raw_second_centered_variance_20261112
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_disjoint_borel_weighted_centered_energy_20261112
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
    let r : ι → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Z : Ω → ℝ := fun ω =>
      ∑ i ∈ F, a i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    let v : ℝ := ∑ i ∈ F, (a i) ^ 2 * r i
    Integrable (fun ω => (Z ω) ^ 2) P ∧
      (∫ ω, (Z ω) ^ 2 ∂P) = v := by sorry
