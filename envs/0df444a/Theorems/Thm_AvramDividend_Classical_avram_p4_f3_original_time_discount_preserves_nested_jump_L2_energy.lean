-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_time_discount_preserves_nested_jump_L2_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_time_discount_preserves_nested_jump_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:39:30.566804+00:00
-- url     : https://prove2.me/theorems/c33c2621-14d7-4051-b817-1cda6c0973be
-- title:
--   Positive physical-time discount preserves original nested small/large Lévy jump L2 source energy
-- statement:
--   For any original physical nonnegative-time product source and Lévy jump band, exp(-qt) with q nonnegative preserves finite quadratic source energy under the two nested time and mark integrals. This applies to stopped original small and large jump martingale integrands, without an equality-in-law replacement.
-- source:
--   Direct double lintegral monotonicity and 0 < exp(-qt) <= 1 on actual nonnegative physical times; this lemma imports neither the canonical source nor residual target.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_time_discount_preserves_nested_jump_L2_energy
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (q : ℝ) (hq : 0 ≤ q)
    (μ : Measure (ℝ≥0 × Ω)) (ν : Measure A)
    (F : (ℝ≥0 × Ω) → A → ℝ)
    (hF : (∫⁻ p, (∫⁻ z, ENNReal.ofReal ((F p z) ^ 2) ∂ν) ∂μ) < ⊤) :
    (∫⁻ p, (∫⁻ z, ENNReal.ofReal
      ((Real.exp (-(q * (p.1 : ℝ))) * F p z) ^ 2) ∂ν) ∂μ) < ⊤ := by sorry
