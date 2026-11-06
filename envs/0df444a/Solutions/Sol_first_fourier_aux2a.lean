-- Prove2me | solution 1 for first_fourier_aux2a
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:26:23.416197+00:00
-- url     : https://prove2.me/submissions/31393ac3-212a-4e21-98d8-bb4d253103c6

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

set_option autoImplicit true
open Real
open Complex hiding log
variable {n : ℕ} {x y : ℝ}

theorem solution :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hπ]
