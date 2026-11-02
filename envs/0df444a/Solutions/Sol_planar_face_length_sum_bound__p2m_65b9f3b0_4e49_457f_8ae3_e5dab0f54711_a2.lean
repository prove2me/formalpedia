-- Prove2me | solution 1 for planar_face_length_sum_bound__p2m_65b9f3b0_4e49_457f_8ae3_e5dab0f54711_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:57.106115+00:00
-- url     : https://prove2.me/submissions/d6009e7b-40b3-4350-b4bf-dec4a29b859e

import Mathlib

set_option autoImplicit false

theorem solution
    (f m : Nat) (length : Fin f → Nat)
    (hsum : (∑ i : Fin f, length i) = 2 * m)
    (hlen : ∀ i : Fin f, 3 ≤ length i) :
    3 * f ≤ 2 * m := by
  have hsum_lower : (∑ i : Fin f, 3) ≤ ∑ i : Fin f, length i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hlen i
  calc
    3 * f = f * 3 := Nat.mul_comm _ _
    _ = ∑ i : Fin f, 3 := by simp
    _ ≤ ∑ i : Fin f, length i := hsum_lower
    _ = 2 * m := hsum