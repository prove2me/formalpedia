-- Prove2me | solution 1 for syracuse_valuation_word_affine_identity
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T00:37:32.736994+00:00
-- url     : https://prove2.me/submissions/aeac7360-f859-4e4e-a95a-0967e826b6a1

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

open Nat

theorem solution (w : List ℕ) (y : ℕ)
    (hword : List.ofFn (fun i : Fin w.length =>
      (3*syracuseStep^[i.val] y+1).factorization 2) = w) :
    2^w.sum * syracuseStep^[w.length] y = 3^w.length*y+syracuseAffineConstant w := by
  induction w generalizing y with
  | nil => simp [syracuseAffineConstant]
  | cons a w ih =>
    let z := syracuseStep y
    have split :
        (3*y+1).factorization 2 :: List.ofFn (fun i : Fin w.length =>
          (3*syracuseStep^[i.val] z+1).factorization 2) = a :: w := by
      rw [List.ofFn_succ] at hword
      simpa only [Fin.val_zero, Function.iterate_zero, id_eq,
        Fin.val_succ, Function.iterate_succ_apply, z] using hword
    obtain ⟨ha, hw⟩ := List.cons.inj split
    have head : 2^a*z=3*y+1 := by
      rw [← ha]
      exact Nat.ordProj_mul_ordCompl_eq_self (3*y+1) 2
    simp only [List.sum_cons, List.length_cons, Function.iterate_succ_apply,
      syracuseAffineConstant]
    calc
      2^(a+w.sum)*syracuseStep^[w.length] z =
          2^a*(2^w.sum*syracuseStep^[w.length] z) := by rw [pow_add, Nat.mul_assoc]
      _ = 2^a*(3^w.length*z+syracuseAffineConstant w) := by rw [ih z hw]
      _ = 3^w.length*(2^a*z)+2^a*syracuseAffineConstant w := by ring
      _ = _ := by rw [head, pow_succ (3:ℕ)]; ring
