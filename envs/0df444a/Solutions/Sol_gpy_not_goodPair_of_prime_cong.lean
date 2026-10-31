-- Prove2me | solution 1 for gpy_not_goodPair_of_prime_cong
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T21:17:37.536112+00:00
-- url     : https://prove2.me/submissions/7a4c8295-3a9a-4af5-ad0d-55e652a10adb

/- Submission file for `gpy` publish3 defect-control problem `gpy_not_goodPair_of_prime_cong`.
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

theorem goodPair_noncong_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    {p : ℕ} (hp : Nat.Prime p) (hg : (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) {j : Fin k}
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

theorem solution {k : ℕ} {h d e : Fin k → ℕ}
    {i : Fin k} {p : ℕ} (hp : Nat.Prime p) {j : Fin k}
    (hj : p ∣ Nat.lcm (d j) (e j)) (hcong : h i ≡ h j [MOD p]) :
    ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := fun hg => goodPair_noncong_aux hp hg hj hcong
