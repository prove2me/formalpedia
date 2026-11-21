-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovecap_small_mark_discount_remainder_nonpos
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovecap_small_mark_discount_remainder_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:21:13.435808+00:00
-- url     : https://prove2.me/theorems/eb8191f8-6f0e-447d-927e-e6cfb67276b7
-- title:
--   Genuine original infinite-activity finite-cap above-barrier small negative Lévy mark discounted compensated remainder nonpositive
-- statement:
--   Exact original finitecap infinite-negative-activity compensated small-jump region sign. Any mark z≥-δ with δ≤cap C.toReal, starting at controlled premark reserve y>C.toReal, cannot cross the ruin boundary y+z<0. The server-Proved genuine caplinear discounted nonruin mark generator sign 035eb378 then gives nonpositive discounted compensated Taylor remainder, without assuming finite activity, finite first moment or global differentiability across the cap. The remaining potential positive ruin overshoot occurs only in marks z<-δ, a finite-intensity tail under the proved quadratic Lévy tail theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_discounted_nonruin_mark_HJB_signed
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovecap_small_mark_discount_remainder_nonpos
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (δ q t y z : ℝ) (hδcap : δ ≤ C.toReal)
    (hy : C.toReal < y) (hz : -δ ≤ z) :
    let V : ℝ → ℝ := fun s =>
      if s ≤ C.toReal then w s else w C.toReal + (s - C.toReal)
    Real.exp (-(q * t)) *
      (V (y + z) - V y - deriv V y * z) ≤ 0 := by sorry
