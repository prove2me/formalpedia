-- Prove2me | solution 1 for taylor_wiles_primes_existence
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T03:15:48.479743+00:00
-- url     : https://prove2.me/submissions/df7b39ac-20cf-41ed-8d73-522d75ba8f91

import Theorems.Thm_flt_odd_prime_ge_5

theorem solution
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_hab : Nat.Coprime a b) (_hbc : Nat.Coprime b c)
    (_hac : Nat.Coprime a c) (heq : a ^ p + b ^ p = c ^ p) :
    False := by
  exact (flt_odd_prime_ge_5 p hp h5 a b c ha hb hc) heq
