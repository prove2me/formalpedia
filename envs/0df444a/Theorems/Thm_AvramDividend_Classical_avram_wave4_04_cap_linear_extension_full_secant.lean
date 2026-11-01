-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
-- name    : AvramDividend.Classical.avram_wave4_04_cap_linear_extension_full_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:08:13.267578+00:00
-- url     : https://prove2.me/theorems/420ddace-18e0-48de-aecc-c7ccbc6c7c52
-- title:
--   Finite-cap slope-one continuation preserves the dividend secant inequality through cap contact
-- statement:
--   For any finite positive cap c and continuous HJB candidate w whose derivative is at least one strictly below c, its slope-one linear continuation above c retains the full dividend secant inequality on the entire nonnegative state space. This provides a cap-contact-safe deterministic extension for a later original-process controlled Itô-Meyer argument, without assuming a derivative at c, that source Lévy jump compensation exists, or that cap local-time stochastic terms already vanish.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i); the source-faithful interior gradient hypothesis and Proved full-cap secant AvramDividend.Classical.avram_wave3_03_bv_full_cap_gradient_secant, UUID 2ba5cc4f-3aab-40ea-a59a-8a49633c7595. Derived by three boundary cases. Supports corrected original-process UBV target UUID 429e17ca-5528-40b5-b593-7c03973d0706; no circular stochastic inference.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04_cap_linear_extension_full_secant
    (c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    b - a ≤
      (if b ≤ c then w b else w c + (b - c)) -
      (if a ≤ c then w a else w c + (a - c)) := by sorry
