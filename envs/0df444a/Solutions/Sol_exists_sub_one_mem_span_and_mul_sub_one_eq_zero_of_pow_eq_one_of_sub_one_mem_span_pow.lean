-- Prove2me | solution 1 for exists_sub_one_mem_span_and_mul_sub_one_eq_zero_of_pow_eq_one_of_sub_one_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b9ba504a-05aa-5dd9-920e-f92cca9b3ad1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_sub_one_mem_span_and_mul_sub_one_eq_zero_of_pow_eq_one_of_sub_one_mem_span_pow
set_option autoImplicit false

theorem solution
    (p : ℕ) (hp : p.Prime) (q : ℕ) (hq : q ≠ 0)
    (T : Type*) [CommRing T] (htf : ∀ x : T, (p : T) * x = 0 → x = 0)
    (u : T) (hu : u ^ q = 1)
    (hN : u - 1 ∈ Ideal.span {((p : T) ^ (padicValNat p q + 1))}) :
    ∃ a : T, a - 1 ∈ Ideal.span {(p : T)} ∧ a * (u - 1) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set k := padicValNat p q with hk
  set P : T := (p : T) ^ (k + 1) with hP

  obtain ⟨m, hqm⟩ : p ^ k ∣ q := pow_padicValNat_dvd
  have hpm : ¬ p ∣ m := by
    intro hdiv
    have : p ^ (k + 1) ∣ q := by
      rw [hqm, pow_succ]; exact Nat.mul_dvd_mul_left _ hdiv
    exact pow_succ_padicValNat_not_dvd hq this
  have hqT : (q : T) = (p : T) ^ k * (m : T) := by
    have : (q : T) = ((p ^ k * m : ℕ) : T) := by rw [hqm]
    rw [this]; push_cast; ring

  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hN
  have hu1 : u = 1 + t * P := by rw [hP, ht]; ring

  have hz : ∀ i : ℕ, ∃ z : T, u ^ i = 1 + P * z := by
    intro i
    induction i with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      exact ⟨z + t + P * z * t, by rw [pow_succ, hz, hu1]; ring⟩
  choose z hz using hz

  have hy : (∑ i ∈ Finset.range q, u ^ i) = (q : T) + P * ∑ i ∈ Finset.range q, z i := by
    calc (∑ i ∈ Finset.range q, u ^ i) = ∑ i ∈ Finset.range q, (1 + P * z i) :=
          Finset.sum_congr rfl (fun i _ => hz i)
      _ = (q : T) + P * ∑ i ∈ Finset.range q, z i := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Finset.mul_sum]
          simp
  set y := ∑ i ∈ Finset.range q, z i with hydef

  have hgeom : (∑ i ∈ Finset.range q, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]

  have hmain : t * ((m : T) + (p : T) * y) = 0 := by
    have e1 : (∑ i ∈ Finset.range q, u ^ i) * (u - 1)
        = (p : T) ^ (2 * k + 1) * (t * ((m : T) + (p : T) * y)) := by
      rw [hy, ← ht, hqT, hP]; ring
    have h1 : (p : T) ^ (2 * k + 1) * (t * ((m : T) + (p : T) * y)) = 0 := by rw [← e1, hgeom]
    have hcancel : ∀ n : ℕ, ∀ x : T, (p : T) ^ n * x = 0 → x = 0 := by
      intro n
      induction n with
      | zero => intro x hx; simpa using hx
      | succ n ih =>
        intro x hx
        apply ih
        apply htf
        rw [← mul_assoc, ← pow_succ']
        exact hx
    exact hcancel _ _ h1

  have hcop : Nat.Coprime m p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm)
  obtain ⟨m', hm'⟩ : ∃ m' : ℤ, (m : ℤ) * m' ≡ 1 [ZMOD p] := Int.mod_coprime hcop
  obtain ⟨r, hr⟩ := Int.modEq_iff_dvd.mp hm'.symm
  have hrT : (m : T) * (m' : T) - 1 = (p : T) * (r : T) := by
    have h := congrArg (fun z : ℤ => (z : T)) hr
    push_cast at h
    linear_combination h
  refine ⟨(m' : T) * ((m : T) + (p : T) * y), ?_, ?_⟩
  · rw [Ideal.mem_span_singleton']
    exact ⟨(r : T) + (m' : T) * y, by linear_combination (-1 : T) * hrT⟩
  · rw [← ht]
    linear_combination ((m' : T) * P) * hmain

end S_exists_sub_one_mem_span_and_mul_sub_one_eq_zero_of_pow_eq_one_of_sub_one_mem_span_pow
end P2MW
export P2MW.S_exists_sub_one_mem_span_and_mul_sub_one_eq_zero_of_pow_eq_one_of_sub_one_mem_span_pow (solution)
