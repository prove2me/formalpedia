-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_time_weight_factor
-- name    : AvramDividend.Classical.gaussian_double_tail_time_weight_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:51:50.172703+00:00
-- url     : https://prove2.me/theorems/0b4d9b1a-285d-4fdc-892e-4061002bfeee
-- title:
--   Exact time-Laplace-weight factorisation of Gaussian double-tail atom
-- statement:
--   The double-tail integrand with time-dependent Esscher-Laplace factor exp(−θt) is exactly that positive ENNReal constant times the unweighted jump atom, for all t,z, splitting by the strict order region 0<t<z. Prove by ENNReal.ofReal_mul under z−t≥0 and commutative multiplication. This allows the weight to be pulled through the jump integral and then removed using ENNReal.mul_lt_top_iff.
-- source:
--   Pinned ENNReal.ofReal_mul and elementary strict-order indicator reasoning; no Open theorem dependencies.

import Mathlib
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_double_tail_time_weight_factor (φ θ t z : ℝ) :
    (if 0 < t ∧ t < z then
      ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
        ENNReal.ofReal (Real.exp (-φ * z))
     else 0) =
    ENNReal.ofReal (Real.exp (-θ * t)) *
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) := by sorry
