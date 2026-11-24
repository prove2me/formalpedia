-- Prove2me | solution 1 for syracuse_affine_prefix_realizes_odd_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T17:39:04.760797+00:00
-- url     : https://prove2.me/submissions/5431aea7-8901-480d-a102-81d60f1b3c45

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

open Nat

private theorem headExponent (a v : ℕ) (hv : ¬ 2 ∣ v) :
    (2^a*v).factorization 2 = a := by
  have hv0 : v ≠ 0 := by rintro rfl; exact hv (dvd_zero _)
  rw [Nat.factorization_mul (Nat.two_pow_pos a).ne' hv0, Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hv,
    Finsupp.single_eq_same, Nat.add_zero]

/-- One affine equation realizes the entire finite word when the terminal
    value is odd. Positivity of the entries forces all inputs to be odd too. -/
theorem solution (w : List ℕ) (y z : ℕ)
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a) (hz : ¬ 2 ∣ z)
    (h : 2^w.sum*z = 3^w.length*y + syracuseAffineConstant w) :
    syracuseStep^[w.length] y = z ∧
    List.ofFn (fun i : Fin w.length =>
      (3*syracuseStep^[i.val] y+1).factorization 2) = w ∧
    ¬ 2 ∣ y := by
  induction w generalizing y with
  | nil =>
    have e : z=y := by simpa [syracuseAffineConstant] using h
    subst y
    simpa using hz
  | cons a w ih =>
    have ha := hpos a (by simp)
    have ht : ∀ b : ℕ, b ∈ w → 0 < b := fun b hb => hpos b (List.mem_cons_of_mem _ hb)
    have full : 2^a*(2^w.sum*z) = 3^w.length*(3*y+1)+2^a*syracuseAffineConstant w := by
      calc
        _ = 2^(a+w.sum)*z := by rw [pow_add, Nat.mul_assoc]
        _ = 3^(w.length+1)*y + (3^w.length+2^a*syracuseAffineConstant w) := h
        _ = _ := by rw [pow_succ]; ring
    have hdiv : 2^a ∣ 3^w.length*(3*y+1) :=
      (Nat.dvd_add_left (dvd_mul_right (2^a) (syracuseAffineConstant w))).mp
        (full ▸ dvd_mul_right _ _)
    have co : ((2:ℕ)^a).Coprime (3^w.length) :=
      ((by decide : Nat.Coprime 2 3).pow_left a).pow_right w.length
    obtain ⟨v,hv⟩ := co.dvd_of_dvd_mul_left hdiv
    have evenHead : 2 ∣ 3*y+1 := (dvd_pow_self 2 ha.ne').trans ⟨v,hv⟩
    have hy : ¬ 2 ∣ y := by omega
    have tail : 2^w.sum*z = 3^w.length*v + syracuseAffineConstant w := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a)
      rw [full,hv]
      ring
    obtain ⟨hend,hword,hvodd⟩ := ih v ht tail
    have hstep : syracuseStep y = v := by
      unfold syracuseStep
      rw [hv]
      exact Nat.ordCompl_pow_mul_of_not_dvd a Nat.prime_two hvodd
    have hfirst : (3*y+1).factorization 2 = a := by
      rw [hv]
      exact headExponent a v hvodd
    refine ⟨?_, ?_, hy⟩
    · simpa only [List.length_cons, Function.iterate_succ_apply, hstep] using hend
    · rw [List.ofFn_succ]
      simpa only [Fin.val_zero, Function.iterate_zero, id_eq, hfirst,
        Fin.val_succ, Function.iterate_succ_apply, hstep] using congrArg (List.cons a) hword
