-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger165_uniform_mesh_discount_rate_scaling
-- name    : AvramDividend.Classical.avram_gledger165_uniform_mesh_discount_rate_scaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:55:57.764741+00:00
-- url     : https://prove2.me/theorems/9e7ea616-849f-4775-adfa-0ce215f5fe49
-- title:
--   Exact numerical scaling of uniform-grid quadratic and boundary Euler errors
-- statement:
--   An exact real-algebra inequality that converts the already established deterministic finite interior plus one boundary Euler error, under mesh width n divided by m plus one, into a uniform constant divided by m plus one. The nonnegative remainder is exactly the positive quadratic coefficient divided by the squared mesh count. Necessary final arithmetic for original gledger161 once gledger164 applies.
-- source:
--   Elementary exact uniform mesh real arithmetic, based on original gledger149 finite error form.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gledger165_uniform_mesh_discount_rate_scaling
    (n m : ℕ) (q K : ℝ) (hK : 0 ≤ K) :
    let δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
    (m : ℝ) * ((q * δ) ^ 2 * K) + 2 * q * δ * K ≤
      ((q * (n : ℝ)) ^ 2 * K + 2 * q * (n : ℝ) * K) /
        ((m : ℝ) + 1) := by sorry
