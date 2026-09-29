-- Prove2me | solution 1 for mme_CW_q6_doubled_hash_AP_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:42:48.674646+00:00
-- url     : https://prove2.me/submissions/5567385e-2b82-41da-9df4-92271d1212d8

import Mathlib.Tactic.Ring
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open MME BigOperators

theorem solution
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin (2 * N) → R)
    (x y z : CWQ6CoupledAddress N)
    (hsupp : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress x y z)) :
    cwQ6DoubledXHash b0 w (x 0) +
        cwQ6DoubledYHash b0 w (y 1) =
      2 * cwQ6DoubledZHash b0 w (z 2) := by
  simp only [cwQ6DoubledXHash, cwQ6DoubledYHash,
    cwQ6DoubledZHash]
  ring_nf
  rw [Finset.sum_mul]
  rw [add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  specialize hsupp j
  change
    (x 0 j = 0 ∧ y 1 j = 0 ∧ z 2 j = 0) ∨
    (x 0 j = 1 ∧ y 1 j = 1 ∧ z 2 j = 1) ∨
    (x 0 j = 0 ∧ y 1 j = 1 ∧ z 2 j = 2) ∨
    (x 0 j = 1 ∧ y 1 j = 0 ∧ z 2 j = 2) at hsupp
  rcases hsupp with h | h | h | h
  all_goals
    rcases h with ⟨hx, hy, hz⟩
    simp [hx, hy, hz, cwQ6CoupledZHashCode] <;> ring
