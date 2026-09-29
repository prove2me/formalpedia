-- Prove2me | solution 1 for invGamma_neg_nat_deriv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:29:41.516757+00:00
-- url     : https://prove2.me/submissions/585b2879-03b7-400c-832e-c6d120de64ef

import Mathlib

open Complex


theorem solution (n : ℕ) :
    deriv (fun s : ℂ => (Gamma s)⁻¹) (-(n : ℂ)) ≠ 0 := by
  let F : ℂ → ℂ := fun s => (Gamma s)⁻¹
  have hF : Differentiable ℂ F := differentiable_one_div_Gamma
  have hrec (s : ℂ) : deriv F s = F (s + 1) + s * deriv F (s + 1) := by
    have heq : F = id * (F ∘ fun z => z + 1) := by
      funext z
      simpa [F] using one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z
    have hcomp :=
      hF.differentiableAt.hasDerivAt.comp s ((hasDerivAt_id s).add_const 1)
    calc
      deriv F s = deriv (id * (F ∘ fun z => z + 1)) s :=
        congrArg (fun f : ℂ → ℂ => deriv f s) heq
      _ = F (s + 1) + s * deriv F (s + 1) := by
        simpa only [Function.comp_apply, id_eq, one_mul, mul_one] using
          ((hasDerivAt_id s).mul hcomp).deriv
  induction n with
  | zero =>
      rw [hrec]
      simp [F, Gamma_one]
  | succ n ih =>
      rw [hrec]
      have hshift : (-(↑(n + 1) : ℂ)) + 1 = -(n : ℂ) := by
        push_cast
        ring
      rw [hshift]
      have hFzero : F (-(n : ℂ)) = 0 := by
        simp [F, Gamma_neg_nat_eq_zero]
      rw [hFzero, zero_add]
      exact mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)) ih
