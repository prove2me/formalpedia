-- Prove2me | solution 1 for gpy_abs_defectCoeff_le_lambdaMass
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T06:48:14.071011+00:00
-- url     : https://prove2.me/submissions/f9483d52-cd8b-4d49-b6ca-e007dd7c4113

/- Submission file for `gpy` publish3 defect-control problem `gpy_abs_defectCoeff_le_lambdaMass`.
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

theorem combinedLcm_pos_aux {k : ℕ} {R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R))
    (he : e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)) :
    0 < Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) := by
  have hd1 : ∀ j, 1 ≤ d j := fun j =>
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1 j)).1
  have he1 : ∀ j, 1 ≤ e j := fun j =>
    (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp he).1 j)).1
  exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
    (fun j _ => Nat.lcm_ne_zero (by have h1 := hd1 j; omega)
      (by have h2 := he1 j; omega)))

theorem solution {k : ℕ} (h : Fin k → ℕ)
    (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    abs (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) ≤
      (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R), abs (lam d)) *
        (∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R), abs (lam e)) := by
  calc abs (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
           else 0))
      ≤ ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R), abs (∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
           else 0)) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R), abs (lam d * lam e) := by
        apply Finset.sum_le_sum
        intro d hd
        calc abs (∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
                  lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
                 else 0))
            ≤ ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R), abs (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
                  lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
                 else 0) := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R), abs (lam d * lam e) := by
              apply Finset.sum_le_sum
              intro e he
              by_cases hc : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              · rw [if_pos hc]
                have hLpos := combinedLcm_pos_aux hd he
                have hL1 : (1 : ℝ) ≤
                    ((Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) : ℕ) : ℝ) := by
                  exact_mod_cast hLpos
                have hLabs : abs (((Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) : ℕ) : ℝ))
                    = ((Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) : ℕ) : ℝ) :=
                  abs_of_nonneg (Nat.cast_nonneg _)
                rw [abs_div, hLabs]
                exact div_le_self (abs_nonneg _) hL1
              · rw [if_neg hc]
                rw [abs_zero]
                exact abs_nonneg _
    _ = ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          (abs (lam d) * abs (lam e)) := by
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro e _
        rw [abs_mul]
    _ = (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R), abs (lam d)) *
          (∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R), abs (lam e)) :=
      (Finset.sum_mul_sum _ _ _ _).symm
