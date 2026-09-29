-- Prove2me | solution 2 for flt_wiles
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T03:31:07.142013+00:00
-- url     : https://prove2.me/submissions/b3028967-197c-4120-8924-f0ea7d5f3e57

import Theorems.Thm_flt_odd_prime_ge_5

theorem solution
    (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p := by
  have h5 : 5 ≤ p := by omega
  exact flt_odd_prime_ge_5 p hp h5 a b c ha hb hc
