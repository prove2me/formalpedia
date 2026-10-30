-- Prove2me | solution 1 for gpy_combinedLcm_pos
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:10:35.476662+00:00
-- url     : https://prove2.me/submissions/ce79c256-b520-4b0a-aae8-3e4964c4fe27

/- Submission file for the Prove2Me problem `gpy_combinedLcm_pos` (publish2 first-moment batch).
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

theorem solution {k : ℕ} {R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R))
    (he : e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)) :
    0 < Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) := by
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
