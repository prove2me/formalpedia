-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_borel_mark_centered_isometry_20261112
-- name    : AvramDividend.Classical.avram_a21_original_bounded_borel_mark_centered_isometry_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:40:59.98319+00:00
-- url     : https://prove2.me/theorems/226cbbdf-16ac-4aa2-b206-8c221b53bd52
-- title:
--   Original physical compensated bounded Borel mark integral exact square isometry
-- statement:
--   For a standing spectrally negative Lévy process on its actual original probability space, and any measurable bounded mark function on a finite negative strip, the source marked integral centred by its true original Lévy intensity has integrable square and exact second moment time times the squared mark intensity.
-- source:
--   Proved original raw first and second Borel marked moments 4106f6a7-d069-4504-a840-d5b32edca1d5 and Proved real centred second moment identity aaeb5fe2-0651-4268-94dc-15c93c7ac2a4; physical marked integral defined from original jump measure. Avram–Palmowski–Pistorius 2007 Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja28_original_bounded_mark_raw_first_second_moments
import Theorems.Thm_AvramDividend_Classical_avram_a21_raw_second_centered_variance_20261112
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_bounded_borel_mark_centered_isometry_20261112
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (g : ℝ → ℝ),
      Measurable g →
      (∀ z ∈ Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), |g z| ≤ 1) →
      ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let J : Ω → ℝ := fun ω =>
        ∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂NX ω
      let r : ℝ := (t : ℝ) * (∫ z in S, g z ∂X.ν)
      let q : ℝ := (t : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
      Integrable (fun ω => (J ω - r) ^ 2) P ∧
        (∫ ω, (J ω - r) ^ 2 ∂P) = q := by sorry
