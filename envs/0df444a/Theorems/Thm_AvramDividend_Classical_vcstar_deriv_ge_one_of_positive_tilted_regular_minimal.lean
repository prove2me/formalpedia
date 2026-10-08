-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_positive_tilted_regular_minimal
-- name    : AvramDividend.Classical.vcstar_deriv_ge_one_of_positive_tilted_regular_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T12:22:48.525108+00:00
-- url     : https://prove2.me/theorems/3ebf451f-30bb-468a-9621-903801a444c3
-- title:
--   Canonical c-star derivative bound from regularity positive tilt and argmin
-- statement:
--   If the candidate scale function W is continuously differentiable on the positive half-line, positive on that half-line, and has positive exponential tilt preserving monotonicity with cstar at zero or a positive global derivative minimum, then vcstar is differentiable and its derivative is at least one. This isolates inputs needed by official milestone 4.
-- source:
--   Formal child for official AvramDividend.Classical milestone d42fc3e4-7a32-428c-80a3-1827a721cf4f; source m4/m4_conditional_reduction.lean, sha256=917724f5dab5b09ebeaf63b7ffe914e25785072d97647502eed867c26a61efe1

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal
open Set
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_deriv_ge_one_of_positive_tilted_regular_minimal (W : ℝ → ℝ)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpositive : ∀ x : ℝ, 0 < x → 0 < W x)
    (φ : ℝ) (hφ : 0 < φ)
    (htilt : MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0))
    (hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) :
    ∀ x : ℝ, 0 < x → DifferentiableAt ℝ (vcstar W) x ∧
      1 ≤ deriv (vcstar W) x := by
  sorry
