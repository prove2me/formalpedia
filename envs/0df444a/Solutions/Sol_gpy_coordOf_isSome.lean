-- Prove2me | solution 1 for gpy_coordOf_isSome
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:34:51.07681+00:00
-- url     : https://prove2.me/submissions/2f9e149b-d79c-45ed-bd46-50a3b5d2567d

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def coordOf {k : ℕ} (d : Fin k → ℕ) (p : ℕ) : Option (Fin k) :=
  if hex : ∃ j, p ∣ d j then some (Classical.choose hex) else none

theorem coordOf_isSome_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ} :
    (coordOf d p).isSome ↔ ∃ j, p ∣ d j := by
  unfold coordOf
  by_cases hex : ∃ j, p ∣ d j
  · rw [dif_pos hex]
    simp [hex]
  · rw [dif_neg hex]
    simp [hex]

theorem solution {k : ℕ} {d : Fin k → ℕ} {p : ℕ} :
    ((if hex : ∃ j', p ∣ d j' then some (Classical.choose hex) else none)).isSome ↔
      ∃ j, p ∣ d j :=
  coordOf_isSome_aux
