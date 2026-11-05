-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f2_void_indicator_bonferroni_nat
-- name    : AvramDividend.Classical.avram_p4_f2_void_indicator_bonferroni_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:23:08.442626+00:00
-- url     : https://prove2.me/theorems/e0ebc82d-7cf9-4f96-92f2-b94ac7474233
-- title:
--   Finite-count void indicator sandwiched by its first and second factorial terms
-- statement:
--   For each nonnegative integer jump count, the indicator that at least one jump occurred lies between its first factorial count corrected by half its second factorial count and its first factorial count. The exact pointwise Bonferroni estimate is the algebraic input to the original negative-band zero-count small-horizon intensity slope from its independently proved first and chronological-pair moments.
-- source:
--   Original-process finite-band chronological pair mean d938e9a5 and first mean c1e09ada, with the open original small-time void slope 17372d7a.

import Mathlib
noncomputable section

theorem AvramDividend.Classical.avram_p4_f2_void_indicator_bonferroni_nat (k : ℕ) :
    (k : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / 2 ≤
      (if k = 0 then 0 else (1 : ℝ)) ∧
    (if k = 0 then 0 else (1 : ℝ)) ≤ (k : ℝ) := by sorry
