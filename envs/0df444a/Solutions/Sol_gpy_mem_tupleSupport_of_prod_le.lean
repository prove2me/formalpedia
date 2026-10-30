-- Prove2me | solution 1 for gpy_mem_tupleSupport_of_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T02:54:37.909393+00:00
-- url     : https://prove2.me/submissions/64b8d95d-8639-4123-ac1d-202ae2782b2a

/- Submission file for `gpy_mem_tupleSupport_of_prod_le` (publish2 good-count batch).
Self-contained: imports Mathlib only. The support set is written out
in the statement; no extra cutoff hypothesis is added.
   Top-level `theorem solution` in the problem's exact binder/statement
   form. No sorry tactic, no axioms beyond the standard ones, no platform
   imports. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution {k : ℕ} {R D : ℕ} (hD : D ≤ R) {d : Fin k → ℕ}
    (h1 : ∀ j, 1 ≤ d j) (hprod : ∏ j, d j = D) :
    d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
      (fun d => ∏ i, d i ≤ R) := by
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun i => Finset.mem_Icc.mpr ⟨h1 i, ?_⟩, ?_⟩
  · calc d i ≤ ∏ j', d j' :=
        Finset.single_le_prod' (fun j' _ => h1 j') (Finset.mem_univ i)
      _ = D := hprod
      _ ≤ R := hD
  · rw [hprod]
    exact hD
