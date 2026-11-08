-- Prove2me | solution 1 for syracuse_no_cycle_below_2887463
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T13:41:16.988053+00:00
-- url     : https://prove2.me/submissions/d36ffc5d-dbe0-4ae5-b9f0-f5884764e94b

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_periodic_reaches_one
import Theorems.Thm_syracuse_no_cycle_below_2786502
import Theorems.Thm_syracuse_descent_three_mod_four_2687463_to_2787459
import Theorems.Thm_syracuse_descent_three_mod_four_2787463_to_2887459

/-
  Attribution: adapted from accepted Prove2me submission cbbe7edd-36de-4b3b-b13a-4dc55450f842
  (theorem 8b82562a-08bf-4b83-a7b3-36f0e888a07f, syracuse_no_cycle_below_2786502) by user fizzyinc3
  (0b3e45cf-260e-4cc3-a72e-1086b677e5d0), Apache-2.0 via the Prove2me terms.
  Helpers step_lt_of_one_mod_four, orbit_min_exists, and stepOdd are copied from that submission;
  the descent dispatch delegates w < 2786502 directly to syracuse_no_cycle_below_2786502 and uses
  syracuse_descent_three_mod_four_2687463_to_2787459 and syracuse_descent_three_mod_four_2787463_to_2887459
  on 2786502 ≤ w < 2887463.
-/

set_option autoImplicit false

namespace S214SY2887463

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

theorem descends_band (w : ℕ) (hlow : 2786502 ≤ w) (hlt : w < 2887463) (hodd : Odd w) :
    ∃ t : ℕ, syracuseStep^[t] w < w := by
  have h1 : 1 < w := by omega
  by_cases h4 : w % 4 = 1
  · exact ⟨1, by simpa using step_lt_of_one_mod_four w h1 h4⟩
  have h43 : w % 4 = 3 := by obtain ⟨k, hk⟩ := hodd; omega
  by_cases b0 : w < 2787463
  · obtain ⟨j, rfl⟩ : ∃ j, w = 2687463 + 4 * j := ⟨(w - 2687463) / 4, by omega⟩
    exact syracuse_descent_three_mod_four_2687463_to_2787459 j (by omega)
  · obtain ⟨j, rfl⟩ : ∃ j, w = 2787463 + 4 * j := ⟨(w - 2787463) / 4, by omega⟩
    exact syracuse_descent_three_mod_four_2787463_to_2887459 j (by omega)

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

end S214SY2887463

open S214SY2887463 in
theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hlt : m < 2887463) (hcyc : syracuseStep^[p] m = m) :
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
    by_cases hwlt : w < 2786502
    · exact syracuse_no_cycle_below_2786502 w (b + 1) hwpos (by omega) hwlt hcyc0
    · by_contra hne
      obtain ⟨t, ht⟩ := descends_band w (by omega) (by omega) hwodd
      exact absurd (hmin0 t) (by omega)
  exact syracuse_periodic_reaches_one m (b + 1) (by omega) hcyc ⟨j, by rw [← hw, hw1]⟩
