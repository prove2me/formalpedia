-- Prove2me | solution 1 for gpy_mem_diffPrimeFinset
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T23:01:38.198882+00:00
-- url     : https://prove2.me/submissions/1035105c-5377-462b-b452-b2d8874c77dc

/- Submission file for `gpy` publish3 defect-control problem `gpy_mem_diffPrimeFinset`.
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


theorem solution {k : ℕ} {h : Fin k → ℕ} {i : Fin k}
    {p : ℕ} :
    p ∈ (Finset.univ.filter (fun j : Fin k => j ≠ i)).biUnion
        (fun j => (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors) ↔
      ∃ j, j ≠ i ∧ p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hmem⟩
    rw [Finset.mem_filter] at hj
    exact ⟨j, hj.2, hmem⟩
  · rintro ⟨j, hjne, hmem⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjne⟩, hmem⟩
