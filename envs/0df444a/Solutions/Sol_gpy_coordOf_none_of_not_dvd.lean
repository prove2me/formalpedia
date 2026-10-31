-- Prove2me | solution 1 for gpy_coordOf_none_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:32:45.195988+00:00
-- url     : https://prove2.me/submissions/375fb4fb-8136-4f42-9e95-05de83884c3e

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def coordOf {k : ℕ} (d : Fin k → ℕ) (p : ℕ) : Option (Fin k) :=
  if hex : ∃ j, p ∣ d j then some (Classical.choose hex) else none

theorem coordOf_none_of_not_dvd_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (h : ¬ ∃ j, p ∣ d j) : coordOf d p = none := by
  unfold coordOf
  rw [dif_neg h]

theorem solution {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (h : ¬ ∃ j, p ∣ d j) :
    (if hex : ∃ j', p ∣ d j' then some (Classical.choose hex) else none) = none :=
  coordOf_none_of_not_dvd_aux h
