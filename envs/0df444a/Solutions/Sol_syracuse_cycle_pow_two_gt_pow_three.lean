-- Prove2me | solution 1 for syracuse_cycle_pow_two_gt_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:59:15.457142+00:00
-- url     : https://prove2.me/submissions/8fc146ef-6602-4c81-84d4-ba68f31676f8

import Mathlib
import Definitions.Def_syracuseStep

open Nat Finset

theorem solution (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hcyc : syracuseStep^[a] m = m) :
    3 ^ a < 2 ^ (∑ i ∈ Finset.range a, (3 * syracuseStep^[i] m + 1).factorization 2) := by
  set x : ℕ → ℕ := fun i => syracuseStep^[i] m with hx
  have hxpos : ∀ i, 0 < x i := by
    intro i
    induction i with
    | zero => simpa [hx] using hm
    | succ n ih =>
      have : x (n + 1) = ordCompl[2] (3 * x n + 1) := by
        simp [hx, Function.iterate_succ_apply', syracuseStep]
      rw [this]
      exact Nat.ordCompl_pos 2 (by omega)
  -- the defining identity of one Syracuse step
  have key : ∀ i, 2 ^ ((3 * x i + 1).factorization 2) * x (i + 1) = 3 * x i + 1 := by
    intro i
    have hstep : x (i + 1) = ordCompl[2] (3 * x i + 1) := by
      simp [hx, Function.iterate_succ_apply', syracuseStep]
    rw [hstep]
    exact Nat.ordProj_mul_ordCompl_eq_self (3 * x i + 1) 2
  -- the orbit product is cyclic
  have hshift : ∏ i ∈ range a, x (i + 1) = ∏ i ∈ range a, x i := by
    have h1 : (∏ i ∈ range a, x (i + 1)) * x 0 = ∏ i ∈ range (a + 1), x i :=
      (Finset.prod_range_succ' x a).symm
    have h2 : ∏ i ∈ range (a + 1), x i = (∏ i ∈ range a, x i) * x a :=
      Finset.prod_range_succ x a
    have hxa : x a = x 0 := by simpa [hx] using hcyc
    have hx0 : 0 < x 0 := hxpos 0
    have heq : (∏ i ∈ range a, x (i + 1)) * x 0 = (∏ i ∈ range a, x i) * x 0 := by
      rw [h1, h2, hxa]
    exact Nat.eq_of_mul_eq_mul_right hx0 heq
  -- strict inequality factorwise, then compare the two products
  have hP : 0 < ∏ i ∈ range a, x i := Finset.prod_pos (fun i _ => hxpos i)
  have hprod_lt : ∏ i ∈ range a, (3 * x i) < ∏ i ∈ range a, (3 * x i + 1) := by
    apply Finset.prod_lt_prod_of_nonempty
    · intro i _; have := hxpos i; omega
    · intro i _; omega
    · exact Finset.nonempty_range_iff.mpr (by omega)
  have hL : ∏ i ∈ range a, (3 * x i + 1)
      = 2 ^ (∑ i ∈ range a, (3 * x i + 1).factorization 2) * ∏ i ∈ range a, x i := by
    calc ∏ i ∈ range a, (3 * x i + 1)
        = ∏ i ∈ range a, (2 ^ ((3 * x i + 1).factorization 2) * x (i + 1)) :=
          Finset.prod_congr rfl (fun i _ => (key i).symm)
      _ = (∏ i ∈ range a, 2 ^ ((3 * x i + 1).factorization 2)) * ∏ i ∈ range a, x (i + 1) :=
          Finset.prod_mul_distrib
      _ = 2 ^ (∑ i ∈ range a, (3 * x i + 1).factorization 2) * ∏ i ∈ range a, x i := by
          rw [hshift, Finset.prod_pow_eq_pow_sum]
  have hR : ∏ i ∈ range a, (3 * x i) = 3 ^ a * ∏ i ∈ range a, x i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [hL, hR] at hprod_lt
  exact Nat.lt_of_mul_lt_mul_right hprod_lt

