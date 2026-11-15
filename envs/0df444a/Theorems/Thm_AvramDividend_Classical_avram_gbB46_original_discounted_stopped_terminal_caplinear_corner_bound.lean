-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB46_original_discounted_stopped_terminal_caplinear_corner_bound
-- name    : AvramDividend.Classical.avram_gbB46_original_discounted_stopped_terminal_caplinear_corner_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:21:53.290147+00:00
-- url     : https://prove2.me/theorems/de2f93b1-dc0b-40f2-a274-9615159e70d4
-- title:
--   Original finite-cap discounted stopped postpayment terminal value correction is nonnegative and bounded by the corner defect
-- statement:
--   At every true original nonnegative stopped clock, the nonnegative terminal difference between the original value function and its interior cap-linear extension remains bounded after discounting by the deterministic finite-cap corner defect. This supplies the discounted terminal comparison required for the genuine original Gaussian stopped cash ledger.
-- source:
--   Apply B44 pathwise postpayment caplinear gap and 0<exp(-qt)≤1 for q,t≥0; no surrogate process or artificial admissibility cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB44_original_admissible_finitecap_postpayment_terminal_corner_gap
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB46_original_discounted_stopped_terminal_caplinear_corner_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b : ℝ) (hb0 : 0 ≤ b) (hbC : b ≤ C.toReal)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (t : ℝ≥0)
    (hy0 : 0 ≤ x + X.X t ω - rightLimit D t ω) :
    let y : ℝ := x + X.X t ω - rightLimit D t ω
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    0 ≤ Real.exp (-(q * (t : ℝ))) * (w y - V y) ∧
      Real.exp (-(q * (t : ℝ))) * (w y - V y) ≤
        (w C.toReal - w b) - (C.toReal - b) := by sorry
