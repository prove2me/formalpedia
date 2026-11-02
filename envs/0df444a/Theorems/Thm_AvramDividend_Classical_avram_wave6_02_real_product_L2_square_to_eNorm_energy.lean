-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_real_product_L2_square_to_eNorm_energy
-- name    : AvramDividend.Classical.avram_wave6_02_real_product_L2_square_to_eNorm_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:21:11.421613+00:00
-- url     : https://prove2.me/theorems/d361e4c4-fcf8-423d-ae80-92227cf6ec2e
-- title:
--   Real product L² square energy converts exactly to eNorm exponent two
-- statement:
--   Exact real-valued L² energy normalization used on the original right-continuous predictable space of the controlled Lévy source. Finite ofReal of square lintegral implies the eNorm real-exponent-two energy consumed by the canonical finite-band compensated martingale L² limit theorem. This is a measure-independent algebraic bridge, to be instantiated on the original μ.prod negative Lévy measure, with no assumption of finite small-jump first moment.
-- source:
--   Pinned Mathlib Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ENNReal.ofReal_pow, sq_abs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave6_02_real_product_L2_square_to_eNorm_energy
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ)
    (hSquare : (∫⁻ a, ENNReal.ofReal ((f a) ^ 2) ∂μ) < ⊤) :
    (∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ) < ⊤ := by sorry
