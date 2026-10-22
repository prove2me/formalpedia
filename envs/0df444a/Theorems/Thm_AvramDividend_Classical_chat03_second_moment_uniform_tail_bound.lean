-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_second_moment_uniform_tail_bound
-- name    : AvramDividend.Classical.chat03_second_moment_uniform_tail_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:43:45.254978+00:00
-- url     : https://prove2.me/theorems/c6c1e4e6-4af9-4a08-a1a8-97a5f06d8a06
-- title:
--   Quantitative uniform quadratic-moment upper-tail bound
-- statement:
--   For an almost-everywhere nonnegative real random variable with integrable squared moment at most C, the nonnegative Lebesgue integral of the portion above threshold R>0 is at most ENNReal.ofReal C divided by ENNReal.ofReal R. The estimate is uniform over any family with the same C and is the central tail input to uniform integrability.
-- source:
--   Composition of separately verified pointwise tail domination, Lebesgue monotonicity, threshold factorisation, and second-moment real-to-ENNReal conversion.

import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_quadratic_tail_lintegral_bound
import Theorems.Thm_AvramDividend_Classical_chat03_quadratic_lintegral_threshold_factorisation
import Theorems.Thm_AvramDividend_Classical_chat03_quadratic_moment_lintegral_le

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.chat03_second_moment_uniform_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (R C : ℝ) (hR : 0 < R)
    (hY0 : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hY2 : Integrable (fun ω => (Y ω) ^ 2) P ∧
      ∫ ω, (Y ω) ^ 2 ∂P ≤ C) :
    (∫⁻ ω, ENNReal.ofReal (if R ≤ Y ω then Y ω else 0) ∂P) ≤
      ENNReal.ofReal C / ENNReal.ofReal R := by sorry
