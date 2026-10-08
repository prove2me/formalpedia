-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_geometric_transform_real_reciprocal
-- name    : AvramDividend.Classical.positive_geometric_transform_real_reciprocal
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:22:03.731322+00:00
-- url     : https://prove2.me/theorems/723e5e3c-b8ad-416d-b2a9-83b8872b63bf
-- title:
--   Geometric ENNReal renewal transform simplifies to the reciprocal real gap
-- statement:
--   For positive real δ and s and a nonnegative real J strictly smaller than δs, the ENNReal geometric-renewal expression (1/s)·δ^{-1}·(1−δ^{-1}(J/s))^{-1} is exactly the ENNReal embedding of the real reciprocal (δs−J)^{-1}. This isolates all reciprocal, subtraction, division and finiteness coercion algebra needed to identify the bounded-variation renewal transform with the canonical scale-function transform.
-- source:
--   Pinned Mathlib ENNReal.ofReal_div_of_pos, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_mul and ENNReal.ofReal_sub; elementary ordered-field algebra.

import Mathlib
open scoped ENNReal

theorem AvramDividend.Classical.positive_geometric_transform_real_reciprocal
    (δ s J : ℝ) (hδ : 0 < δ) (hs : 0 < s)
    (hJ : 0 ≤ J) (hgap : J < δ * s) :
    ENNReal.ofReal (1 / s) *
        ((ENNReal.ofReal δ)⁻¹ *
          (1 - (ENNReal.ofReal δ)⁻¹ * ENNReal.ofReal (J / s))⁻¹) =
      ENNReal.ofReal ((δ * s - J)⁻¹) := by sorry
