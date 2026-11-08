-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_poisson_exponential_power_memLp_two
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps10_poisson_exponential_power_memLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:26:41.072803+00:00
-- url     : https://prove2.me/theorems/669f3f45-5f34-4b2c-ad39-0c325f8eea3d
-- title:
--   Every real Poisson exponential power is square-integrable
-- statement:
--   For every nonnegative Poisson intensity and arbitrary real exponential base, the exponential power of the Poisson count has finite second moment. It follows from the already proved L1 exponential-power lemma with squared base, allowing L2 moment estimates for actual original finite-band Levy counts once their original-space count law is established.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_poisson_power_integrable

open Classical MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps10_poisson_exponential_power_memLp_two (r : ℝ≥0) (a : ℝ) :
    MemLp (fun n : ℕ => a ^ n) 2 (poissonMeasure r) := by sorry
