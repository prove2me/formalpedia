-- Prove2me | solution 1 for gpy_goodPair_coord_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:10:33.403491+00:00
-- url     : https://prove2.me/submissions/debc310a-eb06-477f-9267-94d938ec843f

/- Submission file for the Prove2Me problem `gpy_goodPair_coord_eq_one` (publish2 first-moment batch).
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

theorem solution {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hg : ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :
    d i = 1 ∧ e i = 1 := by
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
