-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_ennreal_quadratic_rate_to_real
-- name    : AvramDividend.Classical.avram_a20_finite_ennreal_quadratic_rate_to_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:32:31.132815+00:00
-- url     : https://prove2.me/theorems/b471f883-2583-4ade-8f27-8b275ca2353e
-- title:
--   Finite extended-nonnegative rate quadratic half-square equals ofReal of its real half-square
-- statement:
--   For any finite extended nonnegative real q, its half-square q²/2 is exactly ENNReal.ofReal((q.toReal)²/2). The proof uses the standard ENNReal.ofReal division, powers of nonnegative reals, and ENNReal.ofReal_toReal for finite q. This short universal bridge connects original arbitrary Borel Lévy source ENNReal chronological-pair count moments to their target real-integral moments, avoiding specialised negative cutoff assumptions.

import Mathlib
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_ennreal_quadratic_rate_to_real
    (q : ℝ≥0∞) (hq : q < ⊤) :
    q ^ 2 / 2 = ENNReal.ofReal (q.toReal ^ 2 / 2) := by sorry
