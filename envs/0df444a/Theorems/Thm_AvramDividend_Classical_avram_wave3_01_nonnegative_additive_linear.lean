-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_nonnegative_additive_linear
-- name    : AvramDividend.Classical.avram_wave3_01_nonnegative_additive_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:56:53.140981+00:00
-- url     : https://prove2.me/theorems/287c9796-7509-4110-b4c8-a85b997a5640
-- title:
--   Continuous additive function on nonnegative real heights is linear
-- statement:
--   An additive function defined on all real arguments whose Cauchy equation is known on the nonnegative cone, whose value at zero vanishes, and which is continuous at zero, is linear on the cone. Extend to all reals by odd reflection, prove the extension is additive in the four sign cases and continuous at zero, then invoke Mathlib map_real_smul. This is the exact scalar bridge for logarithms of positive record-discount semigroups.
-- source:
--   Mathlib map_real_smul and continuous_of_continuousAt_zero on pinned 0df444a; Avram Wave3 first-record semigroup original source.

import Mathlib

theorem AvramDividend.Classical.avram_wave3_01_nonnegative_additive_linear
    (g : ℝ → ℝ)
    (hzero : g 0 = 0)
    (hadd : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      g (x + y) = g x + g y)
    (hcont : ContinuousAt g 0) :
    ∀ x : ℝ, 0 ≤ x → g x = x * g 1 := by sorry
