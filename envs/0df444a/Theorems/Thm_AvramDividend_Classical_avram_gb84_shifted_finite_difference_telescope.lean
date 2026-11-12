-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb84_shifted_finite_difference_telescope
-- name    : AvramDividend.Classical.avram_gb84_shifted_finite_difference_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:52:56.789375+00:00
-- url     : https://prove2.me/theorems/24b4fc1d-1066-4dca-bb17-b8c139a791da
-- title:
--   Every shifted finite block of real increments telescopes
-- statement:
--   For an arbitrary real-valued sequence f, the sum of consecutive differences f(a+j+1)-f(a+j) over j=0,...,b-1 equals f(a+b)-f(a). This supports the deterministic block regrouping of two original Gaussian uniform grids in gb83 and gb82.

import Mathlib

theorem AvramDividend.Classical.avram_gb84_shifted_finite_difference_telescope
    (f : ℕ → ℝ) (a b : ℕ) :
    (Finset.range b).sum (fun j => f (a + j + 1) - f (a + j)) =
      f (a + b) - f a := by sorry
