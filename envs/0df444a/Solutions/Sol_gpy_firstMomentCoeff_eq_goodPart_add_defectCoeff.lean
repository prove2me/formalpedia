-- Prove2me | solution 1 for gpy_firstMomentCoeff_eq_goodPart_add_defectCoeff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:22:14.431376+00:00
-- url     : https://prove2.me/submissions/7fb81d43-137d-446e-b1f0-9675bb646b58

/- Submission file for `gpy` publish3 defect-control problem `gpy_firstMomentCoeff_eq_goodPart_add_defectCoeff`.
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


theorem solution {k : ℕ}
    (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0))
      + (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
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
         else 0)) := by
  have hcompat : ∀ (d e : Fin k → ℕ) (i : Fin k),
      (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
        h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))] := by
    intro d e i hg
    obtain ⟨w, hw, -⟩ := hg
    intro i' _ j' _
    have h1 : w + h i' ≡ 0
        [MOD Nat.gcd (Nat.lcm (d i') (e i')) (Nat.lcm (d j') (e j'))] :=
      Nat.modEq_zero_iff_dvd.mpr
        (dvd_trans (Nat.gcd_dvd_left _ _) (hw i'))
    have h2 : w + h j' ≡ 0
        [MOD Nat.gcd (Nat.lcm (d i') (e i')) (Nat.lcm (d j') (e j'))] :=
      Nat.modEq_zero_iff_dvd.mpr
        (dvd_trans (Nat.gcd_dvd_right _ _) (hw j'))
    exact Nat.ModEq.add_left_cancel' w (h1.trans h2.symm)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hc : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]
  · by_cases hg : (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    · rw [if_pos hc, if_pos hg, if_neg (by simp [hg])]
      simp
    · rw [if_pos hc, if_neg hg, if_pos ⟨hc, hg⟩]
      simp
  · rw [if_neg hc, if_neg (fun hg => hc (hcompat d e i hg)),
      if_neg (fun h => hc h.1)]
    simp
