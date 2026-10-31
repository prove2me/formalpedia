-- Prove2me | solution 1 for gpy_defectCoeff_lamSelberg_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T04:23:06.512993+00:00
-- url     : https://prove2.me/submissions/6d9c6b9c-9322-4bd3-b599-be472b79f6ae

/- Submission file for `gpy` publish3 defect-control problem `gpy_defectCoeff_lamSelberg_eq_sq`.
   Self-contained: imports Mathlib only. Top-level `theorem solution`
   in the problem's exact binder/statement form (statement mechanically
   extracted from the restated theorem, textually identical modulo the
   theorem name). No sorry, no axioms beyond the standard ones, no
   platform imports, no smallness claim. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false


theorem solution {k : ℕ} (h : Fin k → ℕ)
    (R : ℕ) (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) *
            (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) *
            (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0) := by
  have hzero : ∀ {d : Fin k → ℕ}, ¬ Squarefree (∏ i, d i) →
      (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
        * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) = 0 := by
    intro d hd
    by_cases hle : ∏ i, d i ≤ R
    · rw [if_pos hle]
      have hmu : (ArithmeticFunction.moebius (∏ i, d i) : ℝ) = 0 := by
        exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
      rw [hmu, zero_mul]
    · rw [if_neg hle]
  have hsplit_d : (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
              Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
           else 0))
      = (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
          ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
            (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
              (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
                Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
             else 0))
        + (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter
            (fun d : Fin k → ℕ => ¬ Squarefree (∏ j, d j)),
            ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
              (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
                (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
                  Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
               else 0)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hzero_d : (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter
        (fun d : Fin k → ℕ => ¬ Squarefree (∏ j, d j)),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
              Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
           else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    rw [Finset.mem_filter] at hd
    apply Finset.sum_eq_zero
    intro e _
    by_cases hc : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    · rw [if_pos hc, hzero hd.2, zero_mul, zero_div]
    · rw [if_neg hc]
  rw [hsplit_d, hzero_d, add_zero]
  apply Finset.sum_congr rfl
  intro d _
  have hsplit_e : (∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
          (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
            Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0))
      = (∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
          (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
              Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
           else 0))
        + (∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter
            (fun e : Fin k → ℕ => ¬ Squarefree (∏ j, e j)),
            (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
              (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
                Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
             else 0)) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hzero_e : (∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter
        (fun e : Fin k → ℕ => ¬ Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
          (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
            Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    rw [Finset.mem_filter] at he
    by_cases hc : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    · rw [if_pos hc, hzero he.2, mul_zero, zero_div]
    · rw [if_neg hc]
  rw [hsplit_e, hzero_e, add_zero]
