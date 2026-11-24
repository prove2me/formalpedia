-- Prove2me | solution 1 for syracuse_exact_contraction_block
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T12:36:53.191555+00:00
-- url     : https://prove2.me/submissions/af2bb345-bad7-4604-a08b-d171c29406e3

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

open Nat

private theorem oneStep (v : ℕ) :
    syracuseStep (1+2*(4*v)) = 1+2*(3*v) := by
  unfold syracuseStep
  rw [show 3*(1+2*(4*v))+1 = 2^2*(1+2*(3*v)) by ring]
  exact Nat.ordCompl_pow_mul_of_not_dvd 2 Nat.prime_two (by omega)

private theorem contract (i v : ℕ) :
    syracuseStep^[i] (1+2*(4^i*v)) = 1+2*(3^i*v) := by
  induction i generalizing v with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, pow_succ' (4:ℕ), Nat.mul_assoc, oneStep,
      show 3*(4^i*v) = 4^i*(3*v) by ring, ih, pow_succ (3:ℕ)]
    ring

theorem solution (d u : ℕ) (hu : 0 < u) :
    let y := 1+2*(4^d*u)
    (∀ i : ℕ, i ≤ d → syracuseStep^[i] y = 1+2*(3^i*(4^(d-i)*u))) ∧
    (∀ i : ℕ, i < d → syracuseStep^[i+1] y < syracuseStep^[i] y) := by
  dsimp only
  have exactVal (i : ℕ) (hi : i ≤ d) :
      syracuseStep^[i] (1+2*(4^d*u)) = 1+2*(3^i*(4^(d-i)*u)) := by
    have e : 4^d*u = 4^i*(4^(d-i)*u) := by
      rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le hi]
    rw [e, contract]
  refine ⟨exactVal, ?_⟩
  intro i hi
  rw [exactVal (i+1) (by omega), exactVal i hi.le, pow_succ,
    show d-i=(d-(i+1))+1 by omega, pow_succ (4:ℕ)]
  have pos : 0 < 3^i*(4^(d-(i+1))*u) :=
    Nat.mul_pos (pow_pos (by decide) _) (Nat.mul_pos (pow_pos (by decide) _) hu)
  have lhs : 1+2*(3^i*3*(4^(d-(i+1))*u)) = 1+6*(3^i*(4^(d-(i+1))*u)) := by ring
  have rhs : 1+2*(3^i*(4^(d-(i+1))*4*u)) = 1+8*(3^i*(4^(d-(i+1))*u)) := by ring
  rw [lhs,rhs]
  omega
