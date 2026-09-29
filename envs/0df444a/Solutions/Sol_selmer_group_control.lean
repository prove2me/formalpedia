-- Prove2me | solution 1 for selmer_group_control
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T03:15:48.109717+00:00
-- url     : https://prove2.me/submissions/350b707b-d1d4-4a13-a4b4-ee6dbf7dfd4c

import Theorems.Thm_flt_odd_prime_ge_5

theorem solution
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_hab : Nat.Coprime a b) (_hbc : Nat.Coprime b c)
    (_hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) :
    False := by
  exact (flt_odd_prime_ge_5 p hp h5 a b c ha hb hc) heq
