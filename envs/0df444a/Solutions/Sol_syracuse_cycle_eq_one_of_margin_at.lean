-- Prove2me | solution 1 for syracuse_cycle_eq_one_of_margin_at
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:41:02.591599+00:00
-- url     : https://prove2.me/submissions/5a2ddee7-ade3-46c9-abdd-6e943e2857e3

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three
import Theorems.Thm_syracuse_cycle_min_upper_bound
import Theorems.Thm_syracuse_no_small_cycle
import Theorems.Thm_syracuse_periodic_reaches_one

open Nat

/-- From an `a`-periodic point, extract a point of the same orbit that is `a`-periodic and
minimal along its whole forward orbit. -/
theorem orbit_min_exists (m a : ℕ) (ha : 0 < a) (hcyc : syracuseStep^[a] m = m) :
    ∃ j : ℕ, syracuseStep^[a] (syracuseStep^[j] m) = syracuseStep^[j] m ∧
      ∀ i : ℕ, syracuseStep^[j] m ≤ syracuseStep^[i] (syracuseStep^[j] m) := by
  classical
  -- the orbit as a finite set of values
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
  -- every iterate of `m` lands in `S`
  have hper : Function.IsPeriodicPt syracuseStep a m := hcyc
  have hmem : ∀ k : ℕ, syracuseStep^[k] m ∈ S := by
    intro k
    have hmod : syracuseStep^[k] m = syracuseStep^[k % a] m := (hper.iterate_mod_apply k).symm
    simp only [hS, Finset.mem_image, Finset.mem_range]
    exact ⟨k % a, Nat.mod_lt _ ha, hmod.symm⟩
  refine ⟨j, ?_, ?_⟩
  · rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hcyc]
  · intro i
    rw [← Function.iterate_add_apply]
    rw [hjeq]
    exact S.min'_le _ (hmem (i + j))

/-- **Uniform cycle-exclusion criterion at a general threshold `B`.** -/
theorem solution (a m B : ℕ) (ha : 0 < a) (hm : 0 < m) (hB : 0 < B)
    (hcyc : syracuseStep^[a] m = m)
    (hsmall : ∀ z b : ℕ, 0 < z → 0 < b → z < B → syracuseStep^[b] z = z → z = 1)
    (hbd : ∀ K : ℕ, 3 ^ a < 2 ^ K → (3 * B + 1) ^ a < 2 ^ K * B ^ a) :
    m = 1 := by
  obtain ⟨j, hcyc0, hmin0⟩ := orbit_min_exists m a ha hcyc
  set z : ℕ := syracuseStep^[j] m with hz
  have hz0 : 0 < z := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [← hcyc0, Function.iterate_succ_apply']
    exact Nat.ordCompl_pos 2 (by omega)
  set K : ℕ := ∑ i ∈ Finset.range a, (3 * syracuseStep^[i] z + 1).factorization 2 with hK
  have h3 : 3 ^ a < 2 ^ K := syracuse_cycle_pow_two_gt_pow_three z a hz0 ha hcyc0
  have hub : 2 ^ K * z ^ a ≤ (3 * z + 1) ^ a :=
    syracuse_cycle_min_upper_bound z a hz0 ha hcyc0 hmin0
  -- the cycle minimum lies below the threshold `B`
  have hle : z < B := by
    by_contra hcon
    push Not at hcon
    have hlin : B * (3 * z + 1) ≤ (3 * B + 1) * z := by nlinarith [hcon]
    have hpow : (B * (3 * z + 1)) ^ a ≤ ((3 * B + 1) * z) ^ a := Nat.pow_le_pow_left hlin a
    rw [Nat.mul_pow, Nat.mul_pow] at hpow
    have hzpos : 0 < z ^ a := Nat.pow_pos hz0
    have hmargin : (3 * B + 1) ^ a * z ^ a < (2 ^ K * B ^ a) * z ^ a :=
      (Nat.mul_lt_mul_right hzpos).mpr (hbd K h3)
    have hchain : B ^ a * (2 ^ K * z ^ a) ≤ B ^ a * (3 * z + 1) ^ a :=
      Nat.mul_le_mul_left _ hub
    nlinarith [hpow, hmargin, hchain]
  have hz1 : z = 1 := hsmall z a hz0 ha hle hcyc0
  exact syracuse_periodic_reaches_one m a ha hcyc ⟨j, by rw [← hz, hz1]⟩
