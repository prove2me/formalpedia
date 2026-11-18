-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_three_disjoint_mark_void_events_factor_20261117
-- name    : AvramDividend.Classical.avram_a27_original_three_disjoint_mark_void_events_factor_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:16:45.676793+00:00
-- url     : https://prove2.me/theorems/fefb8c78-80be-46cd-88c9-5ad1d33eb862
-- title:
--   Three original physical disjoint negative-mark void events have an exact product probability
-- statement:
--   For three pairwise disjoint measurable negative mark sets on the original Lévy source, the probability of simultaneous absence of physical jumps in all three categories equals the product of their separate no-jump probabilities.
-- source:
--   Proved original two-disjoint-mark void factorisation 48b8388b and exact physical marked counting measure union.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Three disjoint original negative mark void events have a factored joint probability. -/

theorem AvramDividend.Classical.avram_a27_original_three_disjoint_mark_void_events_factor_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B C D : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hD : MeasurableSet D)
    (hNegB : B ⊆ Iio (0 : ℝ))
    (hNegC : C ⊆ Iio (0 : ℝ))
    (hNegD : D ⊆ Iio (0 : ℝ))
    (hBC : Disjoint B C) (hBD : Disjoint B D)
    (hCD : Disjoint C D) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (P {ω | NX ω (Ioc 0 T ×ˢ B) = 0 ∧
      NX ω (Ioc 0 T ×ˢ C) = 0 ∧
      NX ω (Ioc 0 T ×ˢ D) = 0}).toReal =
      ((P {ω | NX ω (Ioc 0 T ×ˢ B) = 0}).toReal *
       (P {ω | NX ω (Ioc 0 T ×ˢ C) = 0}).toReal) *
       (P {ω | NX ω (Ioc 0 T ×ˢ D) = 0}).toReal := by sorry
