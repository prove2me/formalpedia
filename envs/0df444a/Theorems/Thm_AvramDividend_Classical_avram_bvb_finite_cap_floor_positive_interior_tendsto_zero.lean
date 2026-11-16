-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_cap_floor_positive_interior_tendsto_zero
-- name    : AvramDividend.Classical.avram_bvb_finite_cap_floor_positive_interior_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:59:09.07874+00:00
-- url     : https://prove2.me/theorems/09723ccf-c10f-488c-95e1-8d93033a1dd9
-- title:
--   Finite positive cap reciprocal mesh floor stays strictly inside cap and converges to zero
-- statement:
--   For any nonzero finite ENNReal cap C, the physical spatial sequence C.toReal/(n+2) is strictly positive, stays below the original cap for every n, and tends to zero in the real topology. This supplies the exact spatial specialisation of the positive-reserve BV HJB and one-sided negative-mark kernel limit at zero without confusing C with its real-valued lift.
-- source:
--   Use ENNReal.toReal_pos, ofReal_lt_iff_lt_toReal and the pinned natural reciprocal atTop convergence after shifting the index by two.

import Mathlib
open Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_finite_cap_floor_positive_interior_tendsto_zero (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤) :
    (∀ n : ℕ, 0 < C.toReal / ((n : ℝ) + 2) ∧
      ENNReal.ofReal (C.toReal / ((n : ℝ) + 2)) < C) ∧
    Tendsto (fun n : ℕ => C.toReal / ((n : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by sorry
