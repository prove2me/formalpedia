-- Prove2me | solution 1 for logGcd_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T14:11:30.461492+00:00
-- url     : https://prove2.me/submissions/16e6eebc-84a6-4a93-99c1-c8d6eee8a2e7

import Mathlib
import Definitions.Def_Loggcd_Lean_loggcd

set_option autoImplicit true
open Finset ArithmeticFunction
variable {ι : Type*} [Fintype ι]
theorem _root_.solution
    (x : ι → ℕ) (hx : ∀ i, 1 ≤ x i) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * Real.log (Nat.gcd (x i) (x j)) := by
  classical
  -- A common divisor pool: the divisors of the product of all the xᵢ.
  set P : ℕ := ∏ i, x i with hP
  have hPne : P ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    exact fun i _ => Nat.one_le_iff_ne_zero.mp (hx i)
  -- The 0/1 real indicator "does d divide xₖ".
  set f : ℕ → ι → ℝ := fun d k => if d ∣ x k then (1 : ℝ) else 0 with hf
  -- Step 1: rewrite each log-gcd as a von-Mangoldt-weighted product of features.
  have key : ∀ i j,
      Real.log (Nat.gcd (x i) (x j))
        = ∑ d ∈ P.divisors, Λ d * f d i * f d j := by
    intro i j
    have hg : Nat.gcd (x i) (x j) ≠ 0 := by
      rw [Ne, Nat.gcd_eq_zero_iff]
      rintro ⟨h, _⟩
      have hxi_ne : (x i) ≠ 0 := (Nat.one_le_iff_ne_zero.mp (hx i))
      have hxj_ne : (x j) ≠ 0 := (Nat.one_le_iff_ne_zero.mp (hx j))
      exact hxi_ne h
      --omega
    have hsub : (Nat.gcd (x i) (x j)).divisors ⊆ P.divisors :=
      Nat.divisors_subset_of_dvd hPne
        ((Nat.gcd_dvd_left _ _).trans (Finset.dvd_prod_of_mem x (Finset.mem_univ i)))
    -- on the divisors of the gcd, both indicators equal 1
    have hgcd : ∀ d ∈ (Nat.gcd (x i) (x j)).divisors, Λ d = Λ d * f d i * f d j := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      have hdi : d ∣ x i := hd.1.trans (Nat.gcd_dvd_left _ _)
      have hdj : d ∣ x j := hd.1.trans (Nat.gcd_dvd_right _ _)
      simp [hf, hdi, hdj]
    -- off the divisors of the gcd, at least one indicator is 0
    have hvanish : ∀ d ∈ P.divisors, d ∉ (Nat.gcd (x i) (x j)).divisors →
        Λ d * f d i * f d j = 0 := by
      intro d _ hd
      rw [Nat.mem_divisors, not_and] at hd
      have hnd : ¬ d ∣ Nat.gcd (x i) (x j) := fun h => hd h hg
      have hnab : ¬ (d ∣ x i ∧ d ∣ x j) := fun h => hnd (Nat.dvd_gcd h.1 h.2)
      rcases not_and_or.mp hnab with h | h <;> simp [hf, h]
    rw [show Real.log (Nat.gcd (x i) (x j))
            = ∑ d ∈ (Nat.gcd (x i) (x j)).divisors, Λ d from vonMangoldt_sum.symm,
        Finset.sum_congr rfl hgcd, Finset.sum_subset hsub hvanish]
  -- Step 2: substitute, interchange sums, and complete the square.
  have hswap :
      ∑ i, ∑ j, c i * c j * Real.log (Nat.gcd (x i) (x j))
        = ∑ d ∈ P.divisors, Λ d * (∑ i, c i * f d i) ^ 2 := by
    simp_rw [key]
    calc
      ∑ i, ∑ j, c i * c j * ∑ d ∈ P.divisors, Λ d * f d i * f d j
          = ∑ i, ∑ j, ∑ d ∈ P.divisors, c i * c j * (Λ d * f d i * f d j) := by
            simp_rw [Finset.mul_sum]
        _ = ∑ i, ∑ d ∈ P.divisors, ∑ j, c i * c j * (Λ d * f d i * f d j) :=
            Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
        _ = ∑ d ∈ P.divisors, ∑ i, ∑ j, c i * c j * (Λ d * f d i * f d j) :=
            Finset.sum_comm
        _ = ∑ d ∈ P.divisors, Λ d * (∑ i, c i * f d i) ^ 2 := by
            refine Finset.sum_congr rfl (fun d _ => ?_)
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun j _ => by ring)
  -- Step 3: Λ ≥ 0 and squares are ≥ 0.
  rw [hswap]
  exact Finset.sum_nonneg (fun d _ => mul_nonneg vonMangoldt_nonneg (sq_nonneg _))
