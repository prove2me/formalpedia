-- Prove2me | solution 1 for syracuse_no_cycle_below_247463936
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T23:16:00.409228+00:00
-- url     : https://prove2.me/submissions/6caa4207-4b0f-4264-b7c5-f64a283ec67f

import Theorems.Thm_syracuse_periodic_reaches_one
import Theorems.Thm_syracuse_no_cycle_below_twenty_million_cutoff
import Theorems.Thm_syracuse_descent_coprime_to_six_20971520_to_33554432
import Theorems.Thm_syracuse_descent_coprime_to_six_33554432_to_46137344
import Theorems.Thm_syracuse_descent_coprime_to_six_46137344_to_58720256
import Theorems.Thm_syracuse_descent_coprime_to_six_58720256_to_71303168
import Theorems.Thm_syracuse_descent_coprime_to_six_71303168_to_83886080
import Theorems.Thm_syracuse_descent_coprime_to_six_83886080_to_96468992
import Theorems.Thm_syracuse_descent_coprime_to_six_96468992_to_109051904
import Theorems.Thm_syracuse_descent_coprime_to_six_109051904_to_121634816
import Theorems.Thm_syracuse_descent_coprime_to_six_121634816_to_134217728
import Theorems.Thm_syracuse_descent_coprime_to_six_134217728_to_146800640
import Theorems.Thm_syracuse_descent_coprime_to_six_146800640_to_159383552
import Theorems.Thm_syracuse_descent_coprime_to_six_159383552_to_171966464
import Theorems.Thm_syracuse_descent_coprime_to_six_171966464_to_184549376
import Theorems.Thm_syracuse_descent_coprime_to_six_184549376_to_197132288
import Theorems.Thm_syracuse_descent_coprime_to_six_197132288_to_209715200
import Theorems.Thm_syracuse_descent_coprime_to_six_209715200_to_222298112
import Theorems.Thm_syracuse_descent_coprime_to_six_222298112_to_234881024
import Theorems.Thm_syracuse_descent_coprime_to_six_234881024_to_247463936
import Mathlib.Tactic.IntervalCases

/-
  The orbit-minimum argument is adapted from the accepted Prove2me submission for
  syracuse_no_cycle_below_twenty_million_cutoff (theorem b5e0754a-5fbe-48bb-81b6-e9e8b7d41de4)
  by user immiq, Apache-2.0 via the Prove2me terms.
-/

set_option maxRecDepth 100000 in
private theorem band_descends (x : ℕ) (hl : 20971520 ≤ x) (hu : x < 247463936)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by
  have hq := Nat.div_add_mod (x - 20971520) 12582912
  have hr := Nat.mod_lt (x - 20971520) (show 0 < 12582912 by decide)
  generalize (x - 20971520) / 12582912 = k at hq
  generalize (x - 20971520) % 12582912 = r at hq hr
  have hk : k < 18 := by omega
  interval_cases k
  · exact syracuse_descent_coprime_to_six_20971520_to_33554432 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_33554432_to_46137344 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_46137344_to_58720256 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_58720256_to_71303168 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_71303168_to_83886080 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_83886080_to_96468992 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_96468992_to_109051904 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_109051904_to_121634816 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_121634816_to_134217728 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_134217728_to_146800640 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_146800640_to_159383552 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_159383552_to_171966464 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_171966464_to_184549376 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_184549376_to_197132288 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_197132288_to_209715200 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_209715200_to_222298112 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_222298112_to_234881024 x (by omega) (by omega) hodd hthree
  · exact syracuse_descent_coprime_to_six_234881024_to_247463936 x (by omega) (by omega) hodd hthree

theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hlt : m < 247463936)
    (hcycle : syracuseStep^[p] m = m) : m = 1 := by
  let visited (z : ℕ) := ∃ i : ℕ, syracuseStep^[i] m = z
  have hex : ∃ z, visited z := ⟨m,0,rfl⟩
  classical
  let x := Nat.find hex
  obtain ⟨i,hi⟩ := (Nat.find_spec hex : visited x)
  change syracuseStep^[i] m = x at hi
  have xmin (j : ℕ) : x ≤ syracuseStep^[j] x := by
    apply Nat.find_min' hex
    exact ⟨j+i, by rw [Function.iterate_add_apply, hi]⟩
  have hle : x ≤ m := Nat.find_min' hex (show visited m from ⟨0,rfl⟩)
  have xpos : 0 < x := by
    rw [← hi]
    cases i with
    | zero => exact hm
    | succ j => rw [Function.iterate_succ_apply']; exact Nat.ordCompl_pos 2 (by omega)
  have xcycle : syracuseStep^[p] x = x := by
    rw [← hi, ← Function.iterate_add_apply, Nat.add_comm p i, Function.iterate_add_apply, hcycle]
  by_cases small : x < 20971520
  · exact syracuse_periodic_reaches_one m p hp hcycle
      ⟨i, hi.trans (syracuse_no_cycle_below_twenty_million_cutoff x p xpos hp small xcycle)⟩
  · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    let y := syracuseStep^[j] x
    have hy : syracuseStep y = x := by
      rw [hj, Function.iterate_succ_apply'] at xcycle
      exact xcycle
    have ho : ¬ 2 ∣ x := by
      rw [← hy]
      exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3*y+1 ≠ 0)
    have h3 : ¬ 3 ∣ x := by
      intro hdiv
      have he : 2^((3*y+1).factorization 2)*x = 3*y+1 := by
        rw [← hy]
        exact Nat.ordProj_mul_ordCompl_eq_self _ _
      have hd : 3 ∣ 3*y+1 := he ▸ (dvd_mul_of_dvd_right hdiv (2^((3*y+1).factorization 2)))
      omega
    obtain ⟨t,ht⟩ := band_descends x (by omega) (by omega) ho h3
    exact False.elim (Nat.not_lt_of_ge (xmin t) ht)
