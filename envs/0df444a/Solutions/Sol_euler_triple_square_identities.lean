-- Prove2me | solution 1 for euler_triple_square_identities
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T02:47:34.844302+00:00
-- url     : https://prove2.me/submissions/c3b3a046-a2dd-418d-a45b-48d20dc8047f

import Mathlib.Tactic

theorem solution (a b r : Nat) (h : a * b + 1 = r ^ 2) :
    a * (a + b + 2 * r) + 1 = (a + r) ^ 2 ∧ b * (a + b + 2 * r) + 1 = (b + r) ^ 2 := by
  constructor
  · have e : a * (a + b + 2 * r) + 1 = (a * b + 1) + a ^ 2 + 2 * a * r := by ring
    rw [e, h]; ring
  · have e : b * (a + b + 2 * r) + 1 = (a * b + 1) + b ^ 2 + 2 * b * r := by ring
    rw [e, h]; ring
