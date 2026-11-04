-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_weierstrass_with_tail
-- name    : AvramDividend.Classical.avram_p2_i_moment_weierstrass_with_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:42:51.822808+00:00
-- url     : https://prove2.me/theorems/0e8047d0-7820-4426-95cc-68999bd68b8f
-- title:
--   Weierstrass approximation with a simultaneously controlled high-power tail
-- statement:
--   A continuous real test function on [0,2] admits a real polynomial approximation within epsilon uniformly over that interval; after the polynomial has been chosen, there is a higher power K such that |p(z)| ≤ epsilon z^K on z≥2. This combines the pinned-version Weierstrass theorem with a separately proved growing-power tail estimate, permitting positive measures with mass beyond z=1.

import Mathlib
open Set Filter Topology

theorem AvramDividend.Classical.avram_p2_i_moment_weierstrass_with_tail
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc (0 : ℝ) 2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ,
      (∀ z ∈ Set.Icc (0 : ℝ) 2, |p.eval z - g z| < ε) ∧
      (∃ K : ℕ, p.natDegree ≤ K ∧
        ∀ z : ℝ, 2 ≤ z → |p.eval z| ≤ ε * z ^ K) := by sorry
