-- Prove2me | solution 1 for syracuse_smaller_predecessor_iff_affine_interval
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T01:00:05.206029+00:00
-- url     : https://prove2.me/submissions/18a3d200-208b-4808-bfe6-98c3240eae7a

import Theorems.Thm_syracuse_affine_prefix_realizes_odd_endpoint
import Theorems.Thm_syracuse_valuation_word_affine_identity
import Mathlib.Data.Nat.ModEq

open Nat

theorem solution (w : List ℕ) (y n : ℕ)
    (hy : ¬ 2 ∣ y) (hpos : ∀ a : ℕ, a ∈ w → 0 < a) :
    let F := 2^w.sum*y
    let C := syracuseAffineConstant w
    let M := 3^w.length
    (F % M = C % M ∧ C+M ≤ F ∧ F < C+M*n) ↔
      ∃ k : ℕ, 0 < k ∧ k < n ∧ syracuseStep^[w.length] k = y ∧
        List.ofFn (fun i : Fin w.length =>
          (3*syracuseStep^[i.val] k+1).factorization 2) = w ∧ ¬ 2 ∣ k := by
  dsimp only
  let F := 2^w.sum*y
  let C := syracuseAffineConstant w
  let M := 3^w.length
  have hM : 0 < M := pow_pos (by decide) _
  change (F%M=C%M ∧ C+M≤F ∧ F<C+M*n) ↔ _
  constructor
  · rintro ⟨hmod, hlo, hhi⟩
    have hle : C ≤ F := (Nat.le_add_right C M).trans hlo
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp
      (show C ≡ F [MOD M] from hmod.symm)
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro e
      rw [e, Nat.mul_zero, Nat.add_zero] at hk
      omega
    have hksmall : k < n := by
      rw [hk] at hhi
      exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_add_lt_add_left hhi)
    obtain ⟨he, hw, hodd⟩ := syracuse_affine_prefix_realizes_odd_endpoint w k y hpos hy
      (by simpa only [Nat.add_comm] using hk)
    exact ⟨k,hkpos,hksmall,he,hw,hodd⟩
  · rintro ⟨k,hk,hkn,he,hw,_⟩
    have eqn : F = M*k+C := by
      have h := syracuse_valuation_word_affine_identity w k hw
      rw [he] at h
      exact h
    rw [eqn]
    refine ⟨by simp, ?_, ?_⟩
    · have hm := Nat.le_mul_of_pos_right M hk
      omega
    · have hm := Nat.mul_lt_mul_of_pos_left hkn hM
      omega
