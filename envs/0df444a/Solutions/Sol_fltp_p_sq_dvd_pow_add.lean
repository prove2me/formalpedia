-- Prove2me | solution 1 for fltp_p_sq_dvd_pow_add
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T10:41:55.306121+00:00
-- url     : https://prove2.me/submissions/179214a4-fda1-4fda-92e7-36e7e311a5bc

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset in
theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) :
    (p : ℤ) ^ 2 ∣ a ^ p + b ^ p := by
  have hfact : a ^ p + b ^ p = (a + b) * ∑ i ∈ range p, a ^ i * (-b) ^ (p - 1 - i) := by
    have key := (Commute.all a (-b : ℤ)).mul_geom_sum₂ p
    rw [sub_neg_eq_add] at key
    rw [h_odd.neg_pow, sub_neg_eq_add] at key
    exact key.symm
  have hphi : (p : ℤ) ∣ ∑ i ∈ range p, a ^ i * (-b) ^ (p - 1 - i) := by
    have h2 : ((∑ i ∈ range p, a ^ i * (-b) ^ (p - 1 - i) : ℤ) : ZMod p) = 0 := by
      have h0 : ((a + b : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h_dvd
      push_cast at h0 ⊢
      have ha : (a : ZMod p) = -(b : ZMod p) :=
        calc (a : ZMod p)
            = a + 0 := (add_zero _).symm
          _ = a + (-(b : ZMod p) + b) := by
                rw [show (0 : ZMod p) = -(b : ZMod p) + b from (neg_add_cancel _).symm]
          _ = -(b : ZMod p) + (a + b) := add_left_comm _ _ _
          _ = -(b : ZMod p) + 0 := by rw [h0]
          _ = -(b : ZMod p) := add_zero _
      simp_rw [ha]
      have hterm : ∀ i ∈ range p, (-(b : ZMod p)) ^ i * (-(b : ZMod p)) ^ (p - 1 - i) =
          (-(b : ZMod p)) ^ (p - 1) := fun i hi => by
        rw [← pow_add]; congr 1; have hlt : i < p := mem_range.mp hi; omega
      rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
      rw [show (p : ZMod p) = 0 from ZMod.natCast_self p]; simp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2
  rw [hfact, sq]
  exact mul_dvd_mul h_dvd hphi
