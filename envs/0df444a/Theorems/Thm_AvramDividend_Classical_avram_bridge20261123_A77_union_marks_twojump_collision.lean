-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_union_marks_twojump_collision
-- name    : AvramDividend.Classical.avram_bridge20261123_A77_union_marks_twojump_collision
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:25:46.568282+00:00
-- url     : https://prove2.me/theorems/febe926c-8e80-442d-a561-bdf15652a77f
-- title:
--   Original finite-activity Lévy joint mark-family union has quadratic two-jump collision probability bound
-- statement:
--   For the unchanged original spectrally negative Lévy process of finite negative jump intensity, any finite family of measurable negative Borel marks, and a short interval of length δ, the probability of two or more genuine physical jumps whose mark lies in the finite union is bounded by half the square of δ times the union Lévy intensity. Directly instantiate the existing Proved original physical two-jump collision theorem on the measurable negative union. This is the exact O(δ²) ingredient for a fine time-grid multitype Poisson splitting proof.
-- source:
--   Proved Avram original Borel two-jump collision 4ced9f55-3279-4a62-9c0e-61c8454993ae and original n>=2 positive atom frontier af6e786e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bridge20261123_A77_union_marks_twojump_collision
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (δ : ℝ≥0) :
    (P {ω : Ω | (2 : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 δ ×ˢ (⋃ i, B i))).toReal}).toReal ≤
      (((δ : ℝ≥0∞) * X.ν (⋃ i, B i)).toReal) ^ 2 / 2 := by sorry
