-- Prove2me | solution 1 for liouville_transcendental_explicit
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T00:38:43.377422+00:00
-- url     : https://prove2.me/submissions/d5bbfb17-bef3-4d32-b14d-6797567338f5

import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.Localization.Integral

theorem solution :
    Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / 10 ^ n.factorial) := by
  change ¬ IsAlgebraic ℚ (liouvilleNumber 10)
  rw [← IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ]
  exact transcendental_liouvilleNumber (m := 10) (by decide)

#print axioms solution
