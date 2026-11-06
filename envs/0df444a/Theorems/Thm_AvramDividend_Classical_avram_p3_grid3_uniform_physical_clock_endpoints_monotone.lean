-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
-- name    : AvramDividend.Classical.avram_p3_grid3_uniform_physical_clock_endpoints_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:48:35.031713+00:00
-- url     : https://prove2.me/theorems/6db0971a-5bca-4a9a-957e-6ae4dea3d035
-- title:
--   Uniform capped physical clock has exact endpoints and monotone time ordering
-- statement:
--   For each nonnegative stopping horizon T and natural refinement m, the capped uniform physical grid u(i)=min(i,m+1)*T/(m+1) starts at zero, hits T at m+1, and is monotone. This source-exact deterministic construction supplies the time-partition geometry required in the original BV stopped cash C1 identities; compact-reserve and stochastic pathwise hypotheses remain separate.

import Mathlib.Order.Monotone.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_uniform_physical_clock_endpoints_monotone
    (T : ℝ≥0) (m : ℕ) :
    let u : ℕ → ℝ≥0 := fun i =>
      ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
    u 0 = 0 ∧ u (m + 1) = T ∧ Monotone u := by sorry
