-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_continuous_additive_real_linear
-- name    : AvramDividend.Classical.avram_wave3_01_continuous_additive_real_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:54:25.851188+00:00
-- url     : https://prove2.me/theorems/cd937d67-ceda-4126-ab60-49720d248fe0
-- title:
--   The continuous real additive Cauchy equation is linear
-- statement:
--   Every continuous additive real-valued function on the reals is multiplication by its value at 1. We package the function as an additive homomorphism and use Mathlib's pinned real-linearity theorem map_real_smul. This elementary bridge is used after extending the logarithm of the genuine reflected first-record semigroup to negative heights.
-- source:
--   Mathlib.Topology.Instances.RealVectorSpace.map_real_smul, target pinned Mathlib commit; Avram Wave3 original record semigroup.

import Mathlib

theorem AvramDividend.Classical.avram_wave3_01_continuous_additive_real_linear
    (g : ℝ → ℝ)
    (hadd : ∀ x y : ℝ, g (x + y) = g x + g y)
    (hcont : Continuous g) :
    ∀ x : ℝ, g x = x * g 1 := by sorry
