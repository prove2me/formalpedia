-- Prove2me | solution 1 for pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c435173c-a421-5cb6-9c55-91f2d74587fd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
set_option autoImplicit false

theorem solution
    {k : Type*} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] (hq : 5 ≤ q)
    (a : k) (h01728 : a = 0 ∨ a = 1728) (l : k)
    (hl : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
    l ^ (q ^ 2) = l := by
  have hp : q.Prime := Fact.out
  have hqodd : Odd q := hp.odd_of_ne_two (by omega)

  have h2 : (2 : k) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k q] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h3 : (3 : k) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k q] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h16 : (16 : k) ≠ 0 := by
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ h2

  have hfrobC : ∀ n : ℕ, ((OfNat.ofNat n.succ.succ : k)) ^ q = OfNat.ofNat n.succ.succ := by
    intro n
    have := map_ofNat (frobenius k q) n.succ.succ
    rwa [frobenius_def] at this
  have h16q : (16 : k) ^ q = 16 := hfrobC 14
  have h16qq : (16 : k) ^ (q ^ 2) = 16 := by rw [pow_two, pow_mul, h16q, h16q]
  set lam : k := 16 * l with hlam

  have hlamqq : lam ^ (q ^ 2) = lam := by
    rcases h01728 with rfl | rfl
    ·
      have h256 : (256 : k) ≠ 0 := by
        have : (256 : k) = 2 ^ 8 := by norm_num
        rw [this]; exact pow_ne_zero _ h2
      have hP : lam ^ 2 - lam + 1 = 0 := by
        rw [zero_mul] at hl
        have := (mul_eq_zero.mp hl.symm).resolve_left h256
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have h3' : lam ^ 3 = -1 := by linear_combination (lam + 1) * hP
      have h6 : lam ^ 6 = 1 := by
        have : lam ^ 6 = (lam ^ 3) ^ 2 := by ring
        rw [this, h3']; ring
      have hmod : q ^ 2 % 6 = 1 := by
        have h2n : ¬ 2 ∣ q := fun h => by
          rcases hp.eq_one_or_self_of_dvd 2 h with h | h <;> omega
        have h3n : ¬ 3 ∣ q := fun h => by
          rcases hp.eq_one_or_self_of_dvd 3 h with h | h <;> omega
        have : q % 6 = 1 ∨ q % 6 = 5 := by omega
        rw [Nat.pow_mod]
        rcases this with h | h <;> simp [h]
      have hdecomp : q ^ 2 = 6 * (q ^ 2 / 6) + 1 := by
        have := Nat.div_add_mod (q ^ 2) 6
        omega
      rw [hdecomp, pow_add, pow_mul, h6, one_pow, one_mul, pow_one]
    ·
      have hfac : (64 : k) * ((lam + 1) ^ 2 * (lam - 2) ^ 2 * (2 * lam - 1) ^ 2) = 0 := by
        linear_combination (-1 : k) * hl
      have h64 : (64 : k) ≠ 0 := by
        have : (64 : k) = 2 ^ 6 := by norm_num
        rw [this]; exact pow_ne_zero _ h2
      have hprod := (mul_eq_zero.mp hfac).resolve_left h64
      have hlamq : lam ^ q = lam := by
        rcases mul_eq_zero.mp hprod with h | h
        · rcases mul_eq_zero.mp h with h | h
          · have : lam = -1 := by
              have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
              linear_combination this
            rw [this, hqodd.neg_one_pow]
          · have : lam = 2 := by
              have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
              linear_combination this
            rw [this]; exact hfrobC 0
        · have : lam = 2⁻¹ := by
            have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
            field_simp
            linear_combination h'
          rw [this, inv_pow, hfrobC 0]
      rw [pow_two, pow_mul, hlamq, hlamq]

  have hl16 : l = lam / 16 := by rw [hlam]; field_simp
  rw [hl16, div_pow, hlamqq, h16qq]

end S_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728
end P2MW
export P2MW.S_pow_sq_eq_self_of_level_two_value_of_eq_zero_or_eq_1728 (solution)
