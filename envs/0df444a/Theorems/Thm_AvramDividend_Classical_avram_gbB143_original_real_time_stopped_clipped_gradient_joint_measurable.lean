-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB143_original_real_time_stopped_clipped_gradient_joint_measurable
-- name    : AvramDividend.Classical.avram_gbB143_original_real_time_stopped_clipped_gradient_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T09:24:28.247717+00:00
-- url     : https://prove2.me/theorems/5f97452e-d233-455a-bd38-04c0784054bb
-- title:
--   Original real-time stopped clipped Gaussian gradient jointly measurable
-- statement:
--   Transfer the proved B131 stopped clipped coefficient from nonnegative time to real time via measurable Real.toNNReal, correcting the physical discount factor.
-- source:
--   Proved B131 and measurable_real_toNNReal.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB131_original_physical_stopped_clipped_gradient_joint_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB143_original_real_time_stopped_clipped_gradient_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    Measurable (fun z : ℝ × Ω =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X (Real.toNNReal z.1) z.2 - rightLimit D (Real.toNNReal z.1) z.2
      if Real.toNNReal z.1 < ρ z.2 then Real.exp (-(q * z.1)) *
        (if Y ∈ Icc a b then deriv w Y else 1) else 0) := by sorry
