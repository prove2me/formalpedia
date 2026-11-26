-- Prove2me | solution 1 for edenic_semiprime_moebius
-- status  : ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-26T16:55:22.867792+00:00
-- url     : https://prove2.me/submissions/ba0ac48a-1d6e-428e-8925-7516ff3869da

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem solution (n : ℕ) (h : IsEdenicSemiprime n) :
    ArithmeticFunction.moebius n = 1 := by
  obtain ⟨p, hp, hp2, rfl⟩ := h
  have h1 : ArithmeticFunction.moebius (p * (p + 2)) =
      ArithmeticFunction.moebius p * ArithmeticFunction.moebius (p + 2) :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (twin_primes_coprime p hp hp2)
  rw [ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_prime hp2] at h1
  norm_num at h1
  exact h1

-- #44
