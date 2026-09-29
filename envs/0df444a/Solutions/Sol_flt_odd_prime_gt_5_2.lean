-- Prove2me | solution 2 for flt_odd_prime_gt_5
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T03:31:06.672549+00:00
-- url     : https://prove2.me/submissions/c36821ac-997c-4922-9bac-ba5c16f06832

import Theorems.Thm_flt_odd_prime_ge_5

theorem solution
    (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p := by
  have h5 : 5 ≤ p := by omega
  exact flt_odd_prime_ge_5 p hp h5 a b c ha hb hc
