-- Prove2me | solution 1 for gpy_defectIPart_eq_compat_lcm_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:44:20.968442+00:00
-- url     : https://prove2.me/submissions/a08072eb-4f5f-4def-af38-e0af79e11366

/- Submission file for `gpy` publish3 defect-control problem `gpy_defectIPart_eq_compat_lcm_ne_one`.
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

theorem goodPair_coord_eq_one_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hg : (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) : d i = 1 ∧ e i = 1 := by
  obtain ⟨w, hw, hcop⟩ := hg
  have hdvd1 : Nat.lcm (d i) (e i) ∣ w + h i := hw i
  have hdvdL : Nat.lcm (d i) (e i)
      ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
    Finset.dvd_lcm (Finset.mem_univ i)
  have hgcd : Nat.lcm (d i) (e i)
      ∣ Nat.gcd (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
    Nat.dvd_gcd hdvd1 hdvdL
  rw [hcop.gcd_eq_one] at hgcd
  have hlcm1 : Nat.lcm (d i) (e i) = 1 := Nat.dvd_one.mp hgcd
  constructor
  · exact Nat.dvd_one.mp (hlcm1 ▸ Nat.dvd_lcm_left (d i) (e i))
  · exact Nat.dvd_one.mp (hlcm1 ▸ Nat.dvd_lcm_right (d i) (e i))

theorem solution {k : ℕ} (h : Fin k → ℕ)
    (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧
              Nat.lcm (d i) (e i) ≠ 1
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              Nat.lcm (d i) (e i) ≠ 1
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0) := by
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hc : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
  · by_cases hl : Nat.lcm (d i) (e i) ≠ 1
    · have hnotgood : ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := by
        intro hg
        obtain ⟨hd1, he1⟩ := goodPair_coord_eq_one_aux hg
        apply hl
        rw [hd1, he1]
        simp
      rw [if_pos ⟨hc, hnotgood, hl⟩, if_pos ⟨hc, hl⟩]
    · rw [if_neg (fun hcon => hl hcon.2.2), if_neg (fun hcon => hl hcon.2)]
  · rw [if_neg (fun hcon => hc hcon.1), if_neg (fun hcon => hc hcon.1)]
