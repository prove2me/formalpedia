-- Prove2me | solution 1 for section5_l2_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:26.87624+00:00
-- url     : https://prove2.me/submissions/71746cf5-8c3c-4b97-87a0-7e2ec11a74ff

import Mathlib
set_option autoImplicit false
open MeasureTheory
theorem solution {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℂ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  have hi : inner ℂ (hf.toLp f) (hf.toLp f) = ((∫ x, ‖f x‖^2 ∂μ : ℝ) : ℂ) := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hf.coeFn_toLp] with x hx
        rw [hx]
        simp [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
      _ = _ := integral_ofReal
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),hi]
  rfl
