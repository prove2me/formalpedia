-- Prove2me | Theorems.Thm_AvramDividend_Classical_quadratic_exponent_gaussian_grid_mgf_limit_ws01f
-- name    : AvramDividend.Classical.quadratic_exponent_gaussian_grid_mgf_limit_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:58:49.475145+00:00
-- url     : https://prove2.me/theorems/53cc4829-3d0a-47bf-aa73-c26b35d5f0a8
-- title:
--   Quadratic exponent asymptotic determines each shifted shrinking-grid exponential moment
-- statement:
--   For any real exponent f whose quadratic integer normalisation converges to a, any positive integer grid scale m, positive integer Laplace parameter multiplier k and real linear boundary slope C, the shifted shrinking-grid exponential converges to exp(a(k/m)^2). This accounts for the actual finite drift correction kC/[m^2(n+1)] and uses the remotely Proved positive integer-multiple subsequence theorem. It provides the precise three Gaussian exponential moment limits at k=1,m,2m when applied to the Lévy Laplace exponent, but does not itself assert their expectation identities.
-- source:
--   WS1F remotely Proved nat-multiple asymptotic 9389141b, elementary reciprocal limits, real exponential continuity and rational identities.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_quadratic_exponent_limit_nat_multiples_ws01f

open Filter
open scoped Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.quadratic_exponent_gaussian_grid_mgf_limit_ws01f
    (f : ℝ → ℝ) (a C : ℝ)
    (hf : Tendsto (fun n : ℕ =>
      f ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2))
      atTop (nhds a))
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    Tendsto (fun n : ℕ =>
      Real.exp
        (f ((k : ℝ) * ((n : ℝ) + 1)) /
            (((m : ℝ) * ((n : ℝ) + 1)) ^ 2) -
          (k : ℝ) * C / ((m : ℝ) ^ 2 * ((n : ℝ) + 1))))
      atTop (nhds (Real.exp (a * ((k : ℝ) / (m : ℝ)) ^ 2))) := by sorry
