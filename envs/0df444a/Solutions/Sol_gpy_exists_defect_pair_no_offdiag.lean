-- Prove2me | solution 1 for gpy_exists_defect_pair_no_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T01:46:40.768156+00:00
-- url     : https://prove2.me/submissions/cd497c21-144b-4f43-8acd-f8233adcfeac

/- Submission file for `gpy` publish3 defect-control problem `gpy_exists_defect_pair_no_offdiag`.
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


theorem solution :
    ∃ h d e : Fin 1 → ℕ, ∃ i : Fin 1,
      (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
        h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧
      ∀ j : Fin 1, j = i := by
  refine ⟨fun _ => 0, fun _ => 2, fun _ => 1, 0, ?_, ?_, ?_⟩
  · intro i' _ j' _
    have hij : i' = j' := Subsingleton.elim i' j'
    subst hij
    exact Nat.ModEq.refl _
  · rintro ⟨w, hw, hcop⟩
    have hw2 : (2 : ℕ) ∣ w := by
      have h0 := hw 0
      simpa using h0
    have hL2 : (2 : ℕ) ∣
        Finset.lcm (Finset.univ : Finset (Fin 1)) (fun j => Nat.lcm ((fun _ => 2) j) ((fun _ => 1) j)) := by
      have hmem : Nat.lcm 2 1 ∣
          Finset.lcm (Finset.univ : Finset (Fin 1)) (fun j => Nat.lcm ((fun _ => 2) j) ((fun _ => 1) j)) :=
        Finset.dvd_lcm (Finset.mem_univ (0 : Fin 1))
      exact dvd_trans (by decide : (2 : ℕ) ∣ Nat.lcm 2 1) hmem
    have hcop' : Nat.Coprime (w + 0)
        (Finset.lcm (Finset.univ : Finset (Fin 1)) (fun j => Nat.lcm ((fun _ => 2) j) ((fun _ => 1) j))) :=
      hcop
    have hgcd : (2 : ℕ) ∣ Nat.gcd (w + 0)
        (Finset.lcm (Finset.univ : Finset (Fin 1)) (fun j => Nat.lcm ((fun _ => 2) j) ((fun _ => 1) j))) :=
      Nat.dvd_gcd (by simpa using hw2) hL2
    rw [hcop'.gcd_eq_one] at hgcd
    exact (by norm_num : ¬ (2 : ℕ) ∣ 1) hgcd
  · intro j
    exact Subsingleton.elim j 0
