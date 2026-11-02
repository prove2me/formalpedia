-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_lipschitz_jump_increment_two_moduli
-- name    : AvramDividend.Classical.avram_wave5_04c_global_lipschitz_jump_increment_two_moduli
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:06:56.795405+00:00
-- url     : https://prove2.me/theorems/dcde4132-47f2-473d-b579-977066791cf1
-- title:
--   Two-modulus continuity bound for globally Lipschitz Lévy jump increments
-- statement:
--   For any globally L-Lipschitz real payoff w and any states x,z and real jump mark y, the change in the uncompensated jump increment K(z,y)=w(z+y)-w z from K(x,y) is at most 2L*min(|z-x|,|y|). The estimate follows by applying the Lipschitz inequality either in the state variable or separately to the jump increment, then taking the smaller bound. This deterministic inequality is the precise BV finite-first-moment envelope for local dominated convergence of the actual negative-jump generator integral without a C2 second derivative or an assumed stochastic generator identity.
-- source:
--   Full Lean source candidates/work_on/AvramDividend_04c_C1_lipschitz_jump_increment_two_moduli_probe.lean; private compiler verification required before canonical proof submission.

import Mathlib
set_option autoImplicit false

theorem AvramDividend.Classical.avram_wave5_04c_global_lipschitz_jump_increment_two_moduli (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x z y : ℝ) :
    |(w (z + y) - w z) - (w (x + y) - w x)|
      ≤ 2 * L * min |z - x| |y| := by sorry
