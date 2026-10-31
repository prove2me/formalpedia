-- Prove2me | solution 1 for gpy_modEq_of_prime_dvd_natAbs_diff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T22:23:49.496173+00:00
-- url     : https://prove2.me/submissions/e2600272-880c-4fd0-b724-26d8c1fb3756

/- Submission file for `gpy` publish3 defect-control problem `gpy_modEq_of_prime_dvd_natAbs_diff`.
   Self-contained: imports Mathlib only. Top-level `theorem solution`
   in the problem's exact binder/statement form (statement mechanically
   extracted from the restated theorem, textually identical modulo the
   theorem name). No sorry, no axioms beyond the standard ones, no
   platform imports, no smallness claim. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false


theorem solution {p : ℕ} (_hp : Nat.Prime p)
    {a b : ℕ} (hdvd : p ∣ Int.natAbs ((a : ℤ) - (b : ℤ))) :
    a ≡ b [MOD p] := by
  rcases le_total b a with hle | hle
  · have h1 : Int.natAbs ((a : ℤ) - (b : ℤ)) = a - b := by
      rw [← Nat.cast_sub hle, Int.natAbs_natCast]
    rw [h1] at hdvd
    exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm
  · have h1 : Int.natAbs ((a : ℤ) - (b : ℤ)) = b - a := by
      have e : (a : ℤ) - (b : ℤ) = -((b : ℤ) - (a : ℤ)) := by ring
      rw [e, Int.natAbs_neg, ← Nat.cast_sub hle, Int.natAbs_natCast]
    rw [h1] at hdvd
    exact (Nat.modEq_iff_dvd' hle).mpr hdvd
