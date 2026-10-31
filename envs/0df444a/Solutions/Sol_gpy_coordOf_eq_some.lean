-- Prove2me | solution 1 for gpy_coordOf_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:28:33.277202+00:00
-- url     : https://prove2.me/submissions/dc9aaa7e-295d-4607-8e13-4e06239eed98

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def coordOf {k : ℕ} (d : Fin k → ℕ) (p : ℕ) : Option (Fin k) :=
  if hex : ∃ j, p ∣ d j then some (Classical.choose hex) else none

theorem coordOf_eq_some_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (h : coordOf d p = some j) : p ∣ d j := by
  unfold coordOf at h
  by_cases hex : ∃ j, p ∣ d j
  · rw [dif_pos hex] at h
    have hc : Classical.choose hex = j := Option.some.inj h
    rw [← hc]
    exact Classical.choose_spec hex
  · rw [dif_neg hex] at h
    simp at h

theorem solution {k : ℕ} {d : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (h : (if hex : ∃ j', p ∣ d j' then some (Classical.choose hex) else none) = some j) :
    p ∣ d j :=
  coordOf_eq_some_aux h
