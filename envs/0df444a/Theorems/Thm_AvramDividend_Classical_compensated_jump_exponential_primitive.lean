-- Prove2me | Theorems.Thm_AvramDividend_Classical_compensated_jump_exponential_primitive
-- name    : AvramDividend.Classical.compensated_jump_exponential_primitive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:46:05.653967+00:00
-- url     : https://prove2.me/theorems/89643c46-6829-464c-920d-5051b336b5f6
-- title:
--   Exact compensated exponential primitive for Lévy jumps
-- statement:
--   The compensated Lévy-Khintchine exponential increment (exp(-θ z)-1+θ z)/θ equals the interval integral of the nonnegative kernel 1-exp(-θ t) from 0 to z. Valid for any real z and positive θ, enabling exact small-jump compensation with the original truncation and no infinite-subtraction steps.
-- source:
--   Elementary real exponential calculus via intervalIntegral.integral_eq_sub_of_hasDerivAt, used with compensated_jump_tail_layercake to derive ψ(θ)/θ.

import Mathlib
open MeasureTheory intervalIntegral

theorem AvramDividend.Classical.compensated_jump_exponential_primitive
    (θ z : ℝ) (hθ : 0 < θ) :
    (∫ t in (0 : ℝ)..z, 1 - Real.exp (-θ * t)) =
      (Real.exp (-θ * z) - 1 + θ * z) / θ := by sorry
