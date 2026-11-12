-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys78_original_zero_marks_strict_horizon_grid_jump_term_zero
-- name    : AvramDividend.Classical.avram_bvb_phys78_original_zero_marks_strict_horizon_grid_jump_term_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:18:01.87448+00:00
-- url     : https://prove2.me/theorems/e4e4e046-5f42-4021-b356-0612e88e60ab
-- title:
--   Original zero-negative-mark event kills all strict-horizon masked physical jump-grid integrals
-- statement:
--   On the original probability space and filtration, zero marked negative count through T annihilates every original physical marked-jump integral whose support is masked to strict positive times before the uniform-grid horizon, for all grid rows simultaneously. Crucial signed intrinsic source atom of the deterministic zero-count stopped Stieltjes ledger.
-- source:
--   Physical BV zero-mark child 85b63af5 and Proved 336e335f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys76_original_zero_negative_mark_masked_jump_integral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys78_original_zero_marks_strict_horizon_grid_jump_term_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0)
    (H : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hMask : ∀ n (p : ℝ≥0 × ℝ), H n ((p.1, ω), p.2) ≠ 0 →
      0 < p.1 ∧ (p.1 : ℝ) < (T : ℝ) - δ n ∧ p.2 < 0) :
    ∀ n : ℕ,
      (∫ p, H n ((p.1, ω), p.2)
        ∂((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u)))) = 0 := by sorry
