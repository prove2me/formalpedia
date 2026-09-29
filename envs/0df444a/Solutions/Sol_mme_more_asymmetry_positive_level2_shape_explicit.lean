-- Prove2me | solution 1 for mme_more_asymmetry_positive_level2_shape_explicit
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:36:38.284097+00:00
-- url     : https://prove2.me/submissions/6f808627-4061-45a4-aa89-8d61998faf46

import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 4) :
    (a = 1 ∧ b = 1 ∧ c = 2) ∨
      (a = 1 ∧ b = 2 ∧ c = 1) ∨
      (a = 2 ∧ b = 1 ∧ c = 1) := by
  omega
#print axioms solution
