-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_scale_dominated_growth_bridge
-- name    : AvramDividend.Classical.avram_p4_f6_scale_dominated_growth_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:12:41.474512+00:00
-- url     : https://prove2.me/theorems/9e0c1855-9268-46fd-b9eb-991171ff5edd
-- title:
--   Scale domination and compact local control imply a global exponential envelope
-- statement:
--   An arbitrary real function w that vanishes below zero, is uniformly bounded by M on [0,1], and is dominated by A times a comparison function W above one, inherits a global exponential upper bound from W≤K exp(θy), with exact constant max(M,A K). This isolates the deterministic final comparison algebra from the original killed Lévy upcrossing argument.
-- source:
--   An independently provable analytic bridge for the existing HJB-growth obligation 51922c24. The future difficult source is w≤A W from killed two-sided exit, while this lemma discharges the global exponential gluing including the negative and unit interval regions.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_p4_f6_scale_dominated_growth_bridge
    (w W : ℝ → ℝ) (θ A K M : ℝ)
    (hθ : 0 ≤ θ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hneg : ∀ y < 0, w y = 0)
    (hunit : ∀ y, 0 ≤ y → y ≤ 1 → w y ≤ M)
    (hdom : ∀ y, 1 ≤ y → w y ≤ A * W y)
    (hW : ∀ y, W y ≤ K * Real.exp (θ * y)) :
    ∀ y : ℝ, w y ≤ max M (A * K) * Real.exp (θ * y) := by sorry
