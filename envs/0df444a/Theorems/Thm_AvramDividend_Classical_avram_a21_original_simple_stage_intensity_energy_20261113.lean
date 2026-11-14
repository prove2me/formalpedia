-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_stage_intensity_energy_20261113
-- name    : AvramDividend.Classical.avram_a21_original_simple_stage_intensity_energy_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:12:58.477559+00:00
-- url     : https://prove2.me/theorems/089fc430-be3c-4eb2-be02-2ec5beb5c8d9
-- title:
--   Original natural-indexed Borel-simple marked Poisson stage equals exact quadratic intensity
-- statement:
--   For a bounded finite-range Borel negative jump mark, construct finite natural-indexed genuine disjoint physical marked jump cells whose centered sum matches the original compensated marked integral almost surely, whose square is integrable, and whose exact finite energy equals time times the original squared-mark Lévy integral.
-- source:
--   Proved original natural-indexed finite stage d3f5b266-dd21-4c98-8efb-849f40e9ced9 and original full Borel bounded mark compensated isometry 226cbbdf-16ac-4aa2-b206-8c221b53bd52; original marked jump measure and probability space preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_nat_stage_exact_energy_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_borel_mark_centered_isometry_20261112
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_simple_stage_intensity_energy_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n m : ℕ) (hnm : n ≤ m) (t : ℝ≥0)
    (f : SimpleFunc ℝ ℝ)
    (hBound : ∀ z ∈ Ioc (-(1 / ((n : ℝ) + 1)))
       (-(1 / ((m : ℝ) + 1))), |f z| ≤ 1) :
    let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1)))
       (-(1 / ((m : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ),
      (∀ i ∈ Finset.range K, MeasurableSet (B i) ∧ B i ⊆ S) ∧
      (∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K,
        i ≠ j → Disjoint (B i) (B j)) ∧
      let F : Ω → ℝ := fun ω =>
        ∑ i ∈ Finset.range K, c i *
          ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
            (((t : ℝ≥0∞) * X.ν (B i)).toReal))
      let E : ℝ :=
        ∑ i ∈ Finset.range K, (c i)^2 *
          (((t : ℝ≥0∞) * X.ν (B i)).toReal)
      (∀ᵐ ω ∂P, F ω =
        (∫ p in (Ioc 0 t ×ˢ S), f p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, f z ∂X.ν)) ∧
      Integrable (fun ω => (F ω)^2) P ∧
      (∫ ω, (F ω)^2 ∂P) = E ∧
      E = (t : ℝ) * (∫ z in S, (f z)^2 ∂X.ν) := by sorry
