-- Prove2me | solution 1 for mme_CW_2376_doubled_hash_AP_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:57:56.976811+00:00
-- url     : https://prove2.me/submissions/086b9681-6bc1-4dbc-ac2b-46dca7039632

import Definitions.Def_mme_CW_2376_hash_arithmetic

open MME BigOperators

set_option autoImplicit false

theorem solution
    {R : Type} [CommSemiring R] {m : ℕ}
    (b0 : R) (w : Fin (cw2376ProfileLength m) → R)
    (x y z : CW2376ProfileAddress m)
    (hsupp : CW2376CoordinatewiseSupported
      (cw2376MixedAddress x y z)) :
    cw2376DoubledXHash w (x 0) +
        cw2376DoubledYHash b0 w (y 1) =
      2 * cw2376DoubledZHash b0 w (z 2) := by
  simp only [cw2376DoubledXHash, cw2376DoubledYHash,
    cw2376DoubledZHash]
  have hsum :
      (∑ j, (((2 * (x 0 j).val : ℕ) : R) * w j)) +
          (∑ j, (((2 * (y 1 j).val : ℕ) : R) * w j)) =
        2 * ∑ j, (((4 - (z 2 j).val : ℕ) : R) * w j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hj := hsupp j
    change
      (x 0 j).val + (y 1 j).val + (z 2 j).val = 4 at hj
    have hxy :
        (x 0 j).val + (y 1 j).val = 4 - (z 2 j).val := by
      omega
    have hxyR :
        ((x 0 j).val : R) + ((y 1 j).val : R) =
          ((4 - (z 2 j).val : ℕ) : R) := by
      rw [← Nat.cast_add]
      exact congrArg (fun n : ℕ => (n : R)) hxy
    push_cast
    calc
      2 * ((x 0 j).val : R) * w j +
          2 * ((y 1 j).val : R) * w j =
          2 * (((x 0 j).val : R) + ((y 1 j).val : R)) * w j := by
            ring
      _ = 2 * (((4 - (z 2 j).val : ℕ) : R) * w j) := by
            rw [hxyR]
            ring
  calc
    (∑ j, (((2 * (x 0 j).val : ℕ) : R) * w j)) +
          (2 * b0 + ∑ j, (((2 * (y 1 j).val : ℕ) : R) * w j)) =
        2 * b0 +
          ((∑ j, (((2 * (x 0 j).val : ℕ) : R) * w j)) +
            ∑ j, (((2 * (y 1 j).val : ℕ) : R) * w j)) := by
      ac_rfl
    _ = 2 * b0 +
        2 * ∑ j, (((4 - (z 2 j).val : ℕ) : R) * w j) := by
      rw [hsum]
    _ = 2 *
        (b0 + ∑ j, (((4 - (z 2 j).val : ℕ) : R) * w j)) := by
      ring
