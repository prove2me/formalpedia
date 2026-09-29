-- Prove2me | solution 1 for euler_triple_dplus_identity
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T02:47:34.774716+00:00
-- url     : https://prove2.me/submissions/b6cc2c64-9ca9-48b7-9ae7-8372ddbc5008

import Mathlib.Tactic

theorem solution (a b r : Nat) (h : a * b + 1 = r ^ 2) :
    a + b + (a + b + 2 * r) + 2 * a * b * (a + b + 2 * r)
      + 2 * r * (a + r) * (b + r) = 4 * r * (a + r) * (b + r) := by
  linear_combination 2 * (a + b + r) * h
