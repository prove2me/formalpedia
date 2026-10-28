-- Prove2me | solution 1 for syracuse_no_cycle_below_2786502
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:43:43.660877+00:00
-- url     : https://prove2.me/submissions/cbbe7edd-36de-4b3b-b13a-4dc55450f842

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_periodic_reaches_one
import Theorems.Thm_syracuse_descends_below_2310000
import Theorems.Thm_syracuse_descent_odd_band_2310001_to_2387461
import Theorems.Thm_syracuse_descent_three_mod_four_2387463_to_2487459
import Theorems.Thm_syracuse_descent_three_mod_four_2487463_to_2587459
import Theorems.Thm_syracuse_descent_three_mod_four_2587463_to_2687459
import Theorems.Thm_syracuse_descent_three_mod_four_2687463_to_2787459

set_option autoImplicit false

namespace S214SY

theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) :
    syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

theorem descends (w : ℕ) (h1 : 1 < w) (hlt : w < 2786502) (hodd : Odd w) :
    ∃ t : ℕ, syracuseStep^[t] w < w := by
  by_cases hA : w < 2310000
  · exact syracuse_descends_below_2310000 w h1 hA hodd
  by_cases hB : w ≤ 2387461
  · obtain ⟨i, rfl⟩ : ∃ i, w = 2310001 + 2 * i := ⟨(w - 2310001) / 2, by
      obtain ⟨k, hk⟩ := hodd; omega⟩
    obtain ⟨t, -, ht⟩ := syracuse_descent_odd_band_2310001_to_2387461 i (by omega)
    exact ⟨t, ht⟩
  by_cases h4 : w % 4 = 1
  · exact ⟨1, by simpa using step_lt_of_one_mod_four w h1 h4⟩
  have h43 : w % 4 = 3 := by obtain ⟨k, hk⟩ := hodd; omega
  by_cases b0 : w < 2487463
  · obtain ⟨j, rfl⟩ : ∃ j, w = 2387463 + 4 * j := ⟨(w - 2387463) / 4, by omega⟩
    exact syracuse_descent_three_mod_four_2387463_to_2487459 j (by omega)
  by_cases b1 : w < 2587463
  · obtain ⟨j, rfl⟩ : ∃ j, w = 2487463 + 4 * j := ⟨(w - 2487463) / 4, by omega⟩
    exact syracuse_descent_three_mod_four_2487463_to_2587459 j (by omega)
  by_cases b2 : w < 2687463
  · obtain ⟨j, rfl⟩ : ∃ j, w = 2587463 + 4 * j := ⟨(w - 2587463) / 4, by omega⟩
    exact syracuse_descent_three_mod_four_2587463_to_2687459 j (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, w = 2687463 + 4 * j := ⟨(w - 2687463) / 4, by omega⟩
  exact syracuse_descent_three_mod_four_2687463_to_2787459 j (by omega)

theorem orbit_min_exists (m a : ℕ) (ha : 0 < a) (hcyc : syracuseStep^[a] m = m) :
    ∃ j : ℕ, syracuseStep^[a] (syracuseStep^[j] m) = syracuseStep^[j] m ∧
      (∀ i : ℕ, syracuseStep^[j] m ≤ syracuseStep^[i] (syracuseStep^[j] m)) ∧
      syracuseStep^[j] m ≤ m := by
  classical
  set S : Finset ℕ := (Finset.range a).image (fun i => syracuseStep^[i] m) with hS
  have hSne : S.Nonempty := by
    refine ⟨m, ?_⟩
    simp only [hS, Finset.mem_image, Finset.mem_range]
    exact ⟨0, ha, by simp⟩
  obtain ⟨j, hjlt, hjeq⟩ : ∃ j, j < a ∧ syracuseStep^[j] m = S.min' hSne := by
    have := S.min'_mem hSne
    simp only [hS, Finset.mem_image, Finset.mem_range] at this
    obtain ⟨j, hj, hje⟩ := this
    exact ⟨j, hj, hje⟩
  have hper : Function.IsPeriodicPt syracuseStep a m := hcyc
  have hmem : ∀ k : ℕ, syracuseStep^[k] m ∈ S := by
    intro k
    have hmod : syracuseStep^[k] m = syracuseStep^[k % a] m := (hper.iterate_mod_apply k).symm
    simp only [hS, Finset.mem_image, Finset.mem_range]
    exact ⟨k % a, Nat.mod_lt _ ha, hmod.symm⟩
  refine ⟨j, ?_, ?_, ?_⟩
  · rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hcyc]
  · intro i
    rw [← Function.iterate_add_apply, hjeq]
    exact S.min'_le _ (hmem (i + j))
  · have h0 : m ∈ S := by simpa using hmem 0
    rw [hjeq]
    exact S.min'_le _ h0

theorem stepOdd (n : ℕ) : Odd (syracuseStep n) := by
  rw [Nat.odd_iff, ← Nat.not_even_iff]
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * n + 1 ≠ 0) he.two_dvd

end S214SY

open S214SY in
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hlt : m < 2786502) (hcyc : syracuseStep^[p] m = m) :
    m = 1 := by
  obtain ⟨j, hcyc0, hmin0, hwle⟩ := orbit_min_exists m p hp hcyc
  set w : ℕ := syracuseStep^[j] m with hw
  obtain ⟨b, rfl⟩ : ∃ b, p = b + 1 := ⟨p - 1, by omega⟩
  have hwpos : 0 < w := by
    rw [← hcyc0, Function.iterate_succ_apply']
    exact Nat.ordCompl_pos 2 (by omega)
  have hwodd : Odd w := by
    rw [← hcyc0, Function.iterate_succ_apply']
    exact stepOdd _
  have hw1 : w = 1 := by
    by_contra hne
    have h1w : 1 < w := by omega
    obtain ⟨t, ht⟩ := descends w h1w (by omega) hwodd
    exact absurd (hmin0 t) (by omega)
  exact syracuse_periodic_reaches_one m (b + 1) (by omega) hcyc ⟨j, by rw [← hw, hw1]⟩
