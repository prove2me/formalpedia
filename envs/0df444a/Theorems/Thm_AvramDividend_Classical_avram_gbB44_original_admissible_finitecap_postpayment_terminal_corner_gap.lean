-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB44_original_admissible_finitecap_postpayment_terminal_corner_gap
-- name    : AvramDividend.Classical.avram_gbB44_original_admissible_finitecap_postpayment_terminal_corner_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:02:34.24659+00:00
-- url     : https://prove2.me/theorems/86dd3685-e90b-4b35-9e30-3e453bda0224
-- title:
--   Original admissible finite-cap postpayment reserve has terminal caplinear gap bounded by the genuine corner defect
-- statement:
--   For any true original controlled dividend process admissible at finite cap C, its nonnegative postpayment reserve at a physical clock remains within C, and its original value-function terminal gap above an interior caplinear clipping level b is between zero and w(C)-w(b)-(C-b). This discharges the terminal clipping comparison for the original finite-cap Gaussian stopped cash ledger, preserving D and its right limits.
-- source:
--   Combine original admissible postpayment upper bound capped_postPaymentReserve_ofReal_le_cap with B43 closed-band caplinear terminal gap secants, using ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB43_original_finitecap_terminal_caplinear_gap_bounded_by_corner
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB44_original_admissible_finitecap_postpayment_terminal_corner_gap
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
    (ω : Ω) (t : ℝ≥0)
    (hy0 : 0 ≤ x + X.X t ω - rightLimit D t ω) :
    let y : ℝ := x + X.X t ω - rightLimit D t ω
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    0 ≤ w y - V y ∧
      w y - V y ≤ (w C.toReal - w b) - (C.toReal - b) := by sorry
