-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB147_original_real_time_H_fixed_t_exponential_bound
-- name    : AvramDividend.Classical.avram_gbB147_original_real_time_H_fixed_t_exponential_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T11:11:33.475625+00:00
-- url     : https://prove2.me/theorems/14cca2b3-0dd3-4d2f-8656-39a66b4a825f
-- title:
--   Exact physical real-time clipped gradient fixed-time bound
-- statement:
--   B126 bounds the nonnegative-time stopped clipped gradient; the exact real-time gradient differs by an exponential correction. Hence it is bounded in outcomes at every fixed real time, while retaining a uniform bound on nonnegative times.
-- source:
--   Proved B126

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB126_original_physical_postpayment_gradient_uniform_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB147_original_real_time_H_fixed_t_exponential_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let H : ℝ → Ω → ℝ := fun t ω =>
      let s : ℝ≥0 := Real.toNNReal t
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω then Real.exp (-(q * t)) *
        (if Y ∈ Icc a b then deriv w Y else 1)
      else 0
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ω, |H t ω| ≤
        Real.exp (-(q * (t - (Real.toNNReal t : ℝ)))) * B := by sorry
