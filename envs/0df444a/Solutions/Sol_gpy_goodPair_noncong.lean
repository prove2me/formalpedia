-- Prove2me | solution 1 for gpy_goodPair_noncong
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T21:04:38.273997+00:00
-- url     : https://prove2.me/submissions/e3c0a56b-e9c1-4dce-bc33-778e66fef9de

/- Submission file for `gpy` publish3 defect-control problem `gpy_goodPair_noncong`.
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


theorem solution {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    {p : ℕ} (hp : Nat.Prime p)
    (hg : ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) {j : Fin k}
    (hj : p ∣ Nat.lcm (d j) (e j)) : ¬ h i ≡ h j [MOD p] := by
  intro hcong
  obtain ⟨w, hw, hcop⟩ := hg
  have hpw : p ∣ w + h j := dvd_trans hj (hw j)
  have hpwi : p ∣ w + h i :=
    Nat.modEq_zero_iff_dvd.mp
      ((Nat.ModEq.add_left w hcong).trans (Nat.modEq_zero_iff_dvd.mpr hpw))
  have hpL : p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
    dvd_trans hj (Finset.dvd_lcm (Finset.mem_univ j))
  have hpgcd : p ∣ Nat.gcd (w + h i)
      (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
    Nat.dvd_gcd hpwi hpL
  rw [hcop.gcd_eq_one] at hpgcd
  exact hp.not_dvd_one hpgcd
