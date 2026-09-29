-- Prove2me | solution 1 for flt_odd_prime_gt_5
-- status  : ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-15T06:39:50.651896+00:00
-- url     : https://prove2.me/submissions/ceefb08e-8385-48ec-a372-6ec45f9c876e

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_flt_wiles

-- FLT for primes p≥7 follows from Wiles' theorem (Wiles-Taylor 1995).
-- For regular primes, Kummer's earlier proof also works, but Wiles subsumes it.
theorem solution (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ p + b ^ p ≠ c ^ p :=
  flt_wiles p hp h7 a b c ha hb hc
