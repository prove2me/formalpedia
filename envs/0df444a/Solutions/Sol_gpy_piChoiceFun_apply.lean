-- Prove2me | solution 1 for gpy_piChoiceFun_apply
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:39:03.245856+00:00
-- url     : https://prove2.me/submissions/4453a1e8-d3c8-47b3-b981-942c2d177728

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def piChoiceFun {k : ℕ} (s : Finset ℕ)
    (f : ∀ p, p ∈ s → Option (Fin k) × Option (Fin k)) :
    ℕ → Option (Fin k) × Option (Fin k) :=
  fun p => if hp : p ∈ s then f p hp else (none, none)

theorem piChoiceFun_apply_aux {k : ℕ} {s : Finset ℕ}
    {f : ∀ p, p ∈ s → Option (Fin k) × Option (Fin k)} {p : ℕ} (hp : p ∈ s) :
    piChoiceFun s f p = f p hp := by
  unfold piChoiceFun
  rw [dif_pos hp]

theorem solution {k : ℕ} {s : Finset ℕ}
    {f : ∀ p, p ∈ s → Option (Fin k) × Option (Fin k)} {p : ℕ} (hp : p ∈ s) :
    (if hp' : p ∈ s then f p hp' else (none, none)) = f p hp :=
  piChoiceFun_apply_aux hp
