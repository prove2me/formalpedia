-- Prove2me | solution 1 for mme_behrend_explicit_threeAP_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T15:44:45.460295+00:00
-- url     : https://prove2.me/submissions/fd82ebb2-5180-4a03-aaca-78eb0390f5e2

import Mathlib.Combinatorics.Additive.AP.Three.Behrend

open Real

/-!
# An explicit finite Behrend witness

Mathlib proves Behrend's quantitative lower bound through `rothNumberNat`.
This wrapper extracts the maximizing progression-free finset, so laser-method
arguments can use both the set itself and its explicit cardinality bound.
-/

theorem solution (N : ℕ) :
    ∃ S : Finset ℕ,
      S ⊆ Finset.range N ∧
      ThreeAPFree (S : Set ℕ) ∧
      (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤ (S.card : ℝ) := by
  obtain ⟨S, hS_range, hS_card, hS_free⟩ := rothNumberNat_spec N
  refine ⟨S, hS_range, hS_free, ?_⟩
  rw [hS_card]
  exact Behrend.roth_lower_bound
