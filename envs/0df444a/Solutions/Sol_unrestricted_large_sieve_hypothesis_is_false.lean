-- Prove2me | solution 1 for unrestricted_large_sieve_hypothesis_is_false
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-10-03T17:30:43.11786+00:00
-- url     : https://prove2.me/submissions/9fa9464d-7b44-499f-94ba-52097f6e8f05

import Mathlib

noncomputable section

namespace UnrestrictedLargeSieve

def eR (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

def Holds : Prop :=
  ∀ (a : ℤ → ℂ), Summable (fun n : ℤ => ‖a n‖ ^ 2) →
    ∀ (T : Finset ℤ) (xi : ℤ → ℝ) (d u v : ℝ), 0 < d → 1 ≤ v - u →
      (∀ i ∈ T, ∀ j ∈ T, i ≠ j →
        d ≤ |(xi i - xi j) - round (xi i - xi j)|) →
      (∑ i ∈ T, ‖∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋, a n * eR (xi i * (n : ℝ))‖ ^ 2)
        ≤ ((v - u) + 1 / d) * ∑' n : ℤ, ‖a n‖ ^ 2

def coefficients (n : ℤ) : ℂ := if n = 1 ∨ n = 2 then 1 else 0

theorem coefficients_summable : Summable (fun n : ℤ => ‖coefficients n‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := ({1, 2} : Finset ℤ))
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  simp [coefficients, hn]

theorem coefficients_energy : (∑' n : ℤ, ‖coefficients n‖ ^ 2) = (2 : ℝ) := by
  rw [tsum_eq_sum (s := ({1, 2} : Finset ℤ))]
  · norm_num [coefficients]
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp [coefficients, hn]

theorem coefficients_interval_sum :
    (∑ n ∈ Finset.Ioc ⌊(3 / 4 : ℝ)⌋ ⌊(9 / 4 : ℝ)⌋,
      coefficients n * eR (0 * (n : ℝ))) = (2 : ℂ) := by
  have hlow : ⌊(3 / 4 : ℝ)⌋ = (0 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    norm_num
  have hhigh : ⌊(9 / 4 : ℝ)⌋ = (2 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    norm_num
  rw [hlow, hhigh]
  have hinterval : Finset.Ioc (0 : ℤ) 2 = {1, 2} := by decide
  rw [hinterval]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [coefficients, eR]

theorem not_holds : ¬ Holds := by
  intro hLS
  have hbound := hLS coefficients coefficients_summable {0} (fun _ => 0)
    4 (3 / 4) (9 / 4) (by norm_num) (by norm_num) (by simp)
  simp only [Finset.sum_singleton, coefficients_interval_sum, coefficients_energy] at hbound
  norm_num at hbound

end UnrestrictedLargeSieve

theorem solution : ¬ UnrestrictedLargeSieve.Holds := UnrestrictedLargeSieve.not_holds

#print axioms solution

end
