-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite79_original_cap_slack
-- name    : AvramDividend.Classical.avram_gfinite79_original_cap_slack
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:58:51.909423+00:00
-- url     : https://prove2.me/theorems/8d57c7a5-841f-4ac6-b2b5-4d780d143fd6
-- title:
--   Original finite cap fraction has nonnegative verification cash slack
-- statement:
--   Under the exact positive finite-cap, nonnegative-state continuity, interior C2 and derivative-at-least-one conditions of the Avram original-process Gaussian verification theorem, every fractional cap cutoff b=C(j+1)/(j+2) has nonnegative cash slack w(C)-w(b)-(C-b). This supplies the nonnegative deterministic budget used by the eventwise Gaussian cash L1 transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_gfinite79_original_cap_slack
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) :
    0 ≤ (w C.toReal - w (C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
      (C.toReal - C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))) := by
  sorry
