-- Prove2me | solution 1 for flt5_gcd_rs_coprime
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-14T17:06:27.677403+00:00
-- url     : https://prove2.me/submissions/b3f90120-d643-4648-bcf8-a061fe188e39

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

-- Full proof: gcd(r,s)=1 from gcd(w,v)=1 where w=r^5, v=s^5
theorem solution (r s w v : ℤ)
    (hcop : Int.gcd w v = 1) (hr : w = r ^ 5) (hs : v = s ^ 5) :
    Int.gcd r s = 1 := by
  have h5 : IsCoprime (r ^ 5) (s ^ 5) := by
    have : Int.gcd (r ^ 5) (s ^ 5) = 1 := by rw [← hr, ← hs]; exact hcop
    exact Int.isCoprime_iff_gcd_eq_one.mpr this
  have hcop_rs : IsCoprime r s :=
    (IsCoprime.pow_iff (by norm_num) (by norm_num)).mp h5
  exact Int.isCoprime_iff_gcd_eq_one.mp hcop_rs
