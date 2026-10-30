-- Prove2me | solution 1 for gpy_crtResidue_add
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T02:46:16.227254+00:00
-- url     : https://prove2.me/submissions/57326acd-8051-48ff-a6fc-d5afa587206e

/- Submission file for `gpy_crtResidue_add` (publish2 good-count batch).
Self-contained: imports Mathlib only. The statement carries the
crtResidue definition unfolded (there is no standalone crtResidue
theorem in the source file, so no separate crtResidue problem).
   Top-level `theorem solution` in the problem's exact binder/statement
   form. No sorry tactic, no axioms beyond the standard ones, no platform
   imports. -/
import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution {k : ℕ} {h d e : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (hp : Nat.Prime p) (hj : p ∣ Nat.lcm (d j) (e j))
    (hcompat : ∀ j', p ∣ Nat.lcm (d j') (e j') → h j ≡ h j' [MOD p]) :
    (if hex : ∃ j, p ∣ Nat.lcm (d j) (e j)
      then p - h (Classical.choose hex) % p else 0) + h j ≡ 0 [MOD p] := by
  have hex : ∃ j', p ∣ Nat.lcm (d j') (e j') := ⟨j, hj⟩
  rw [dif_pos hex]
  have hj₀dvd : p ∣ Nat.lcm (d (Classical.choose hex)) (e (Classical.choose hex)) :=
    Classical.choose_spec hex
  have hmod : h j ≡ h (Classical.choose hex) [MOD p] := hcompat _ hj₀dvd
  have step1 : (p - h (Classical.choose hex) % p) + h j
      ≡ (p - h (Classical.choose hex) % p) + h (Classical.choose hex) [MOD p] :=
    Nat.ModEq.add_left _ hmod
  have step2 : (p - h (Classical.choose hex) % p) + h (Classical.choose hex)
      ≡ 0 [MOD p] := by
    have hr : h (Classical.choose hex) % p < p := Nat.mod_lt _ hp.pos
    have e : (p - h (Classical.choose hex) % p) + h (Classical.choose hex)
        ≡ (p - h (Classical.choose hex) % p) + (h (Classical.choose hex) % p) [MOD p] :=
      (Nat.ModEq.add_left _ (Nat.mod_modEq _ _)).symm
    have e2 : (p - h (Classical.choose hex) % p) + (h (Classical.choose hex) % p) = p :=
      Nat.sub_add_cancel (le_of_lt hr)
    rw [e2] at e
    exact e.trans ((Nat.modEq_zero_iff_dvd).mpr (dvd_refl p))
  exact step1.trans step2
