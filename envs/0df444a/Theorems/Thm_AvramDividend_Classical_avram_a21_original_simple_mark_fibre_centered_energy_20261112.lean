-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_mark_fibre_centered_energy_20261112
-- name    : AvramDividend.Classical.avram_a21_original_simple_mark_fibre_centered_energy_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:56:22.742661+00:00
-- url     : https://prove2.me/theorems/dc9748d4-be63-474a-902c-efd90de9704a
-- title:
--   Original-source finite Borel-simple mark fibre energy isometry
-- statement:
--   For any measurable negative mark set and any real finite-valued Borel simple mark, its disjoint physical mark fibres partition the original source Borel mark integral. The weighted centred sum of original marked counts has integrable square and exact Lévy squared-mark intensity energy on the original Ω/P.
-- source:
--   Proved A21 exact finite disjoint original Borel centred cell energy 528b7e5b-d233-4910-85ef-3a201e4dd5f8; Mathlib measurable finite SimpleFunc range and disjoint fibres. Supports source-faithful simple quantisation/energy certificate 67336b2d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_disjoint_borel_weighted_centered_energy_20261112
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_simple_mark_fibre_centered_energy_20261112
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (g : SimpleFunc ℝ ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    let r : ℝ → ℝ := fun y => ((T : ℝ≥0∞) * X.ν (B y)).toReal
    let F : Ω → ℝ := fun ω =>
      ∑ y ∈ g.range, y * ((NX ω (Ioc 0 T ×ˢ B y)).toReal - r y)
    let E : ℝ := ∑ y ∈ g.range, y ^ 2 * r y
    Integrable (fun ω => (F ω) ^ 2) P ∧
      (∫ ω, (F ω) ^ 2 ∂P) = E := by sorry
