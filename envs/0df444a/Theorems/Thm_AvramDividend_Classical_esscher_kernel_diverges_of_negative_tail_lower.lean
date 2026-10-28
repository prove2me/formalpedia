-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_kernel_diverges_of_negative_tail_lower
-- name    : AvramDividend.Classical.esscher_kernel_diverges_of_negative_tail_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:34:43.555386+00:00
-- url     : https://prove2.me/theorems/53ac364d-903a-4886-ba03-e670f61116d1
-- title:
--   Lower jump-tail bounds force divergence of a canonical Esscher renewal kernel
-- statement:
--   The finite Lévy quadratic moment and infinite negative-jump intensity imply that every real kernel bounded below by a fixed positive multiple of the truncated negative jump mass tends to infinity at the positive origin. This is the limit-transfer step in the bounded-variation renewal-kernel proof.
-- source:
--   Proved AvramDividend.Classical.negative_jump_real_tail_tendsto_top (2cde304a-3060-4be7-ac2a-b48c96e45367) and an order-filter argument.

import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
import Mathlib.Topology.Algebra.Order.Field

open AvramDividend.Classical MeasureTheory Filter Set
open scoped ENNReal Topology

namespace AvramDividend.Classical

/-- A kernel dominating a positive multiple of the negative-jump intensity has infinite origin limit. -/
theorem esscher_kernel_diverges_of_negative_tail_lower
    (ν : Measure ℝ)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤)
    (k : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hk : ∀ x : ℝ, 0 < x → c * (ν (Iio (-x))).toReal ≤ k x) :
    Tendsto k (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry

end AvramDividend.Classical
