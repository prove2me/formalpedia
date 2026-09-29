-- Prove2me | solution 1 for mme_finite_MM_extraction_swap_double_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:37:26.230797+00:00
-- url     : https://prove2.me/submissions/fed293c6-c823-48d6-967c-9a1fb082c915

import Mathlib.Tactic
import Theorems.Thm_mme_finite_MM_extraction_swap_double

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {k V : ℕ}
    (a b c : Fin k → ℕ) (lower : ℝ)
    (hlower : 0 ≤ lower) (hcount : lower ≤ (k : ℝ))
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
      (cyclicSymmetrization T))
    (hvolume : ∀ j, a j * b j * c j = V) :
    ∃ (q : ℕ) (A B C : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun r ↦ MMObj K (A r) (B r) (C r)))
        (sixSymmetrization T) ∧
      lower ^ (2 : ℕ) ≤ (q : ℝ) ∧
      (∀ r, A r * B r * C r = V ^ 2) := by
  let A : Fin (k * k) → ℕ := fun r ↦
    a (finProdFinEquiv.symm r).1 * c (finProdFinEquiv.symm r).2
  let B : Fin (k * k) → ℕ := fun r ↦
    b (finProdFinEquiv.symm r).1 * b (finProdFinEquiv.symm r).2
  let C : Fin (k * k) → ℕ := fun r ↦
    c (finProdFinEquiv.symm r).1 * a (finProdFinEquiv.symm r).2
  refine ⟨k * k, A, B, C, ?_, ?_, ?_⟩
  · simpa only [A, B, C] using
      mme_finite_MM_extraction_swap_double a b c hrestrict
  · push_cast
    nlinarith [show (0 : ℝ) ≤ k by positivity]
  · intro r
    simp only [A, B, C]
    have hi := hvolume (finProdFinEquiv.symm r).1
    have hj := hvolume (finProdFinEquiv.symm r).2
    calc
      a (finProdFinEquiv.symm r).1 * c (finProdFinEquiv.symm r).2 *
            (b (finProdFinEquiv.symm r).1 * b (finProdFinEquiv.symm r).2) *
          (c (finProdFinEquiv.symm r).1 * a (finProdFinEquiv.symm r).2) =
          (a (finProdFinEquiv.symm r).1 *
              b (finProdFinEquiv.symm r).1 *
              c (finProdFinEquiv.symm r).1) *
            (a (finProdFinEquiv.symm r).2 *
              b (finProdFinEquiv.symm r).2 *
              c (finProdFinEquiv.symm r).2) := by ring
      _ = V * V := by rw [hi, hj]
      _ = V ^ 2 := by rw [pow_two]
