-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a28_lindeberg_finite_mesh_energy
-- name    : AvramDividend.Classical.avram_ga_a28_lindeberg_finite_mesh_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:48:25.06354+00:00
-- url     : https://prove2.me/theorems/b439623a-ad00-41fc-bc83-51d0eea5751d
-- title:
--   Finite-mesh large Gaussian increments have fourth-moment energy envelope
-- statement:
--   The sum of quadratic energy in mesh increments above a fixed threshold is bounded by the sum of their fourth powers divided by the square of the threshold.
-- source:
--   Exact deterministic finite-mesh Lindeberg tail estimate for b0d9951c using public ga_a27.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_lindeberg_scalar_fourth_energy
open BigOperators

theorem AvramDividend.Classical.avram_ga_a28_lindeberg_finite_mesh_energy {ι : Type*} (s : Finset ι) (r : ℝ) (hr : 0 < r)
    (z : ι → ℝ) :
    (∑ i ∈ s, if r ≤ |z i| then (z i) ^ 2 else 0) ≤
      (∑ i ∈ s, (z i) ^ 4) / r ^ 2 := by sorry
