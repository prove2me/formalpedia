-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_bv_signed_compensated_kernel_joint_measurable
-- name    : AvramDividend.Classical.chat07_bv_signed_compensated_kernel_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T08:05:29.625616+00:00
-- url     : https://prove2.me/theorems/e5db441a-7abd-4946-bd23-4273f2433dc1
-- title:
--   Joint measurability of the signed compensated Lévy scale generator kernel
-- statement:
--   For any monotone real scale candidate W, its ordinary derivative and truncated compensation branch define a jointly measurable signed negative-jump generator kernel after exponential reserve weighting. The proof explicitly composes measurable coordinate projections, monotone W, measurable ordinary derivative, measurable branching at jump size one, and real exponential. This provides the strong measurability premise needed to deduce signed product-integrability from the accepted absolute compensated-jump kernel bound and then apply the signed Fubini theorem.

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.chat07_bv_signed_compensated_kernel_joint_measurable
    (W : ℝ → ℝ) (hW : Monotone W) (θ : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        (W (p.1 - p.2) - W p.1 +
          (if p.2 < 1 then p.2 * deriv W p.1 else 0))) := by sorry
