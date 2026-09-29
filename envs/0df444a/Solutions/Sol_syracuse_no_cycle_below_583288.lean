-- Prove2me | solution 1 for syracuse_no_cycle_below_583288
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T18:38:19.746664+00:00
-- url     : https://prove2.me/submissions/54c9568d-ce47-42ed-bd31-b601a1940d1b

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_periodic_reaches_one
import Theorems.Thm_syracuse_descends_below_583288

open Nat

/-- From an `a`-periodic point, extract a point of the same orbit that is `a`-periodic, minimal
along its whole forward orbit, and no larger than the point we started from. -/
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

/-- A cycle minimum cannot descend, so below the verified descent bound the only cycle is `{1}`. -/
theorem solution (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 583287)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by
  obtain ⟨j, hcyc0, hmin0, hwle⟩ := orbit_min_exists z a ha hcyc
  set w : ℕ := syracuseStep^[j] z with hw
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hwpos : 0 < w := by
    rw [← hcyc0, Function.iterate_succ_apply']
    exact Nat.ordCompl_pos 2 (by omega)
  have hwodd : Odd w := by
    rw [← hcyc0, Function.iterate_succ_apply']
    exact stepOdd _
  have hw1 : w = 1 := by
    by_contra hne
    have h1w : 1 < w := by omega
    obtain ⟨t, ht⟩ := syracuse_descends_below_583288 w h1w (by omega) hwodd
    exact absurd (hmin0 t) (by omega)
  exact syracuse_periodic_reaches_one z (b + 1) (by omega) hcyc ⟨j, by rw [← hw, hw1]⟩
