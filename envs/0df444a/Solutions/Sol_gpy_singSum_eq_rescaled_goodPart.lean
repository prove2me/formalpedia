-- Prove2me | solution 1 for gpy_singSum_eq_rescaled_goodPart
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:10:37.673492+00:00
-- url     : https://prove2.me/submissions/90174f63-68e6-45b4-9465-d9fb5be156d9

/- Submission file for the Prove2Me problem `gpy_singSum_eq_rescaled_goodPart` (publish2 first-moment batch).
   Self-contained: imports Mathlib only. Top-level `theorem solution` in the
   problem's exact binder/statement form (statement mechanically extracted
   from the restated theorem, so the two are textually identical modulo
   the theorem name). No sorry tactic, no axioms beyond the standard
   ones, no platform imports. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

theorem solution {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
          ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
         else 0)) =
      ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then
          (((Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) : ℕ) : ℝ) /
            ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)) *
            (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
                h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
             then lam d * lam e /
               Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
             else 0)
         else 0) := by
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
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hg : (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
  · rw [if_pos hg, if_pos hg, if_pos (hcompat d e i hg)]
    have hLpos : 0 < Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) := by
      have hd1 : ∀ j, 1 ≤ d j := by
        have hmem := (Finset.mem_filter.mp hd).1
        intro j
        exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hmem j)).1
      have he1 : ∀ j, 1 ≤ e j := by
        have hmem := (Finset.mem_filter.mp he).1
        intro j
        exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hmem j)).1
      exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
        (fun j _ => Nat.lcm_ne_zero (by have h1 := hd1 j; omega)
          (by have h2 := he1 j; omega)))
    have hLne : ((Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hLpos)
    have hφne : ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Nat.totient_pos.mpr hLpos))
    rw [div_mul_div_comm,
      mul_comm (((Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) : ℕ) : ℝ))
        (lam d * lam e),
      mul_div_mul_right _ _ hLne]
  · rw [if_neg hg, if_neg hg]
