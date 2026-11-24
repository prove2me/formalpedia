-- Prove2me | solution 1 for syracuse_mixed_valuation_prefix_descent_certificate
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T17:39:05.766795+00:00
-- url     : https://prove2.me/submissions/ee6410b2-11fe-44a8-9162-6ca46d81ef6d

import Theorems.Thm_syracuse_affine_prefix_realizes_odd_endpoint
import Mathlib.Tactic.Ring

open Nat

theorem solution (w : List ℕ) (y n : ℕ)
    (hpos : ∀ a : ℕ, a ∈ w → 0 < a)
    (hmod : (3^w.length*y+syracuseAffineConstant w) % 2^(w.sum+1) = 2^w.sum)
    (hbelow : 3^w.length*y+syracuseAffineConstant w < 2^w.sum*n) :
    syracuseStep^[w.length] y < n ∧
      syracuseStep^[w.length] y = (3^w.length*y+syracuseAffineConstant w)/2^w.sum ∧
      List.ofFn (fun i : Fin w.length =>
        (3*syracuseStep^[i.val] y+1).factorization 2) = w := by
  let D := 2^w.sum
  let B := 3^w.length*y+syracuseAffineConstant w
  let b := B/(2*D)
  let z := 1+2*b
  have hd : 0 < D := Nat.two_pow_pos _
  have hp : 2^(w.sum+1) = 2*D := by simp [D, pow_succ, Nat.mul_comm]
  rw [hp] at hmod
  have hdecomp : D+(2*D)*b=B := by
    have e := Nat.mod_add_div B (2*D)
    change B % (2*D) = D at hmod
    simpa only [hmod] using e
  have eqn : D*z=B := by
    calc
      D*z = D+(2*D)*b := by dsimp only [z]; ring
      _ = B := hdecomp
  have ho : ¬2 ∣ z := by dsimp [z]; omega
  obtain ⟨hend,hword,_⟩ := syracuse_affine_prefix_realizes_odd_endpoint w y z hpos ho eqn
  have hz : z < n := Nat.lt_of_mul_lt_mul_left (show D*z < D*n by rwa [eqn])
  refine ⟨hend.trans_lt hz, ?_, hword⟩
  change syracuseStep^[w.length] y = B/D
  rw [hend, ← eqn, Nat.mul_div_cancel_left _ hd]
