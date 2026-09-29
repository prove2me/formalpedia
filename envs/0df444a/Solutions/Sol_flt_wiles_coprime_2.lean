-- Prove2me | solution 2 for flt_wiles_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T03:31:07.486956+00:00
-- url     : https://prove2.me/submissions/dc371f4a-8270-406c-8808-c8a08cd5a89f

import Theorems.Thm_flt_odd_prime_ge_5

theorem solution
    (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_hab : Nat.Coprime a b) (_hbc : Nat.Coprime b c)
    (_hac : Nat.Coprime a c) :
    a ^ p + b ^ p ≠ c ^ p := by
  have h5 : 5 ≤ p := by omega
  exact flt_odd_prime_ge_5 p hp h5 a b c ha hb hc
