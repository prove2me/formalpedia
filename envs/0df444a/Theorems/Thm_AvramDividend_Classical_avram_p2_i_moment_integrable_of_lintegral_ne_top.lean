-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_integrable_of_lintegral_ne_top
-- name    : AvramDividend.Classical.avram_p2_i_moment_integrable_of_lintegral_ne_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:31:27.255754+00:00
-- url     : https://prove2.me/theorems/3f32be6e-6b24-4983-a105-ff3ef8acc7b0
-- title:
--   Finite nonnegative power lintegral yields real moment integrability
-- statement:
--   A nonnegative-supported real measure has an integrable kth real monomial whenever its ENNReal-ofReal kth moment lintegral is finite. This removes the separate Bochner-integrability hypotheses from the source-facing original-process weighted image application; the proof uses the pinned Mathlib equivalence between finite nonnegative lintegral and real integrability plus ENNReal.ofReal_pow.

import Mathlib
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_i_moment_integrable_of_lintegral_ne_top
    (μ : Measure ℝ) (hpositive : ∀ᵐ z ∂μ, 0 ≤ z)
    (k : ℕ)
    (hfinite : (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤) :
    Integrable (fun z : ℝ => z ^ k) μ := by sorry
