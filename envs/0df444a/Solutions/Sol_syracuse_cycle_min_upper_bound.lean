-- Prove2me | solution 1 for syracuse_cycle_min_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T19:06:55.785579+00:00
-- url     : https://prove2.me/submissions/8bb348de-7f3a-4ef4-9d3d-2c098279c9c3

import Mathlib
import Definitions.Def_syracuseStep

open Nat Finset

theorem solution (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hcyc : syracuseStep^[a] m = m)
    (hmin : ∀ i : ℕ, m ≤ syracuseStep^[i] m) :
    2 ^ (∑ i ∈ Finset.range a, (3 * syracuseStep^[i] m + 1).factorization 2) * m ^ a
      ≤ (3 * m + 1) ^ a := by
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
  have hP : 0 < ∏ i ∈ range a, x i := Finset.prod_pos (fun i _ => hxpos i)
  have hmin' : ∀ i, m ≤ x i := by intro i; simpa [hx] using hmin i
  -- one step, weighted by the cycle minimum
  have hstep_le : ∀ i, m * (2 ^ ((3 * x i + 1).factorization 2) * x (i + 1))
      ≤ (3 * m + 1) * x i := by
    intro i
    rw [key i]
    calc m * (3 * x i + 1) = 3 * m * x i + m := by ring
      _ ≤ 3 * m * x i + x i := Nat.add_le_add_left (hmin' i) _
      _ = (3 * m + 1) * x i := by ring
  have hprod_le : ∏ i ∈ range a, (m * (2 ^ ((3 * x i + 1).factorization 2) * x (i + 1)))
      ≤ ∏ i ∈ range a, ((3 * m + 1) * x i) :=
    Finset.prod_le_prod' (fun i _ => hstep_le i)
  have hL : ∏ i ∈ range a, (m * (2 ^ ((3 * x i + 1).factorization 2) * x (i + 1)))
      = (2 ^ (∑ i ∈ range a, (3 * x i + 1).factorization 2) * m ^ a) * ∏ i ∈ range a, x i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      Finset.prod_mul_distrib, hshift, Finset.prod_pow_eq_pow_sum]
    ring
  have hR : ∏ i ∈ range a, ((3 * m + 1) * x i) = (3 * m + 1) ^ a * ∏ i ∈ range a, x i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [hL, hR] at hprod_le
  exact Nat.le_of_mul_le_mul_right hprod_le hP
