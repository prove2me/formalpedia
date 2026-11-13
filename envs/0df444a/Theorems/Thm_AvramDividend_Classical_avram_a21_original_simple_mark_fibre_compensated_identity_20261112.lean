-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_mark_fibre_compensated_identity_20261112
-- name    : AvramDividend.Classical.avram_a21_original_simple_mark_fibre_compensated_identity_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:07:12.119131+00:00
-- url     : https://prove2.me/theorems/c0e79a4d-a516-44bd-bd4f-f4b4e6aece50
-- title:
--   Actual original compensated simple marked integral equals disjoint marked-fibre centred count sum
-- statement:
--   On the original probability space of a finite-activity spectrally negative Lévy process, a bounded real finite-valued Borel mark function integrates against the genuine marked jump measure and is compensated by the actual intensity. Almost surely this equals the finite sum over its disjoint mark fibres of the original marked counts minus each original Poisson intensity.
-- source:
--   Proved original physical a.e. finite-range partition 6509baaf-1f99-477a-b35c-45a69f460b43 and scaled Borel simple-fibre compensator identity ce09bf6a-ada4-43c1-b7fd-dd3f411050bc. Enables original simple marked-cell approximation to genuinely equal the compensated marked integral for A21 67336b2d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_bounded_mark_pathwise_fibre_partition_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_simple_mark_intensity_fibre_sum_20261112
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_simple_mark_fibre_compensated_identity_20261112
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (g : SimpleFunc ℝ ℝ) (hBound : ∀ z ∈ S, |g z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ℝ → Set ℝ := fun y => S ∩ g ⁻¹' {y}
    ∀ᵐ ω ∂P,
      (∑ y ∈ g.range, y *
          ((NX ω (Ioc 0 T ×ˢ B y)).toReal -
            (((T : ℝ≥0∞) * X.ν (B y)).toReal))) =
        (∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω) -
          (T : ℝ) * (∫ z in S, g z ∂X.ν) := by sorry
