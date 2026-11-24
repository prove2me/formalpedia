-- Prove2me | solution 1 for syracuse_contraction_length_iff_dvd
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T17:05:31.351846+00:00
-- url     : https://prove2.me/submissions/992c7965-bef8-4603-9303-c0216e1bd6b6

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

open Nat

private theorem contractionStart (d y : ℕ) (hy : 0 < y) (ho : ¬ 2 ∣ y)
    (steps : ∀ i : ℕ, i < d →
      3*syracuseStep^[i] y+1 = 4*syracuseStep^[i+1] y) :
    2*4^d ∣ y-1 := by
  induction d generalizing y with
  | zero =>
    change 2 ∣ y-1
    omega
  | succ d ih =>
    let z := syracuseStep y
    have hz : 0 < z := Nat.ordCompl_pos 2 (by omega)
    have hzo : ¬ 2 ∣ z := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
    have first : 3*y+1=4*z := by simpa using steps 0 (by omega)
    have rest (i : ℕ) (hi : i < d) :
        3*syracuseStep^[i] z+1 = 4*syracuseStep^[i+1] z := by
      simpa only [z, Function.iterate_succ_apply] using steps (i+1) (by omega)
    obtain ⟨u, hu⟩ := ih z hz hzo rest
    have e : 3*(y-1) = 4*(z-1) := by omega
    have scaled : 3*(y-1) = (2*4^(d+1))*u := by
      rw [e, hu, pow_succ (4:ℕ)]
      ring
    have co : (2*4^(d+1)).Coprime 3 :=
      (by decide : Nat.Coprime 2 3).mul_left ((by decide : Nat.Coprime 4 3).pow_left _)
    exact co.dvd_of_dvd_mul_left ⟨u, scaled⟩

private theorem twoHalvings (w : ℕ) :
    syracuseStep (1+2*(4*w)) = 1+2*(3*w) := by
  unfold syracuseStep
  rw [show 3*(1+2*(4*w))+1 = 2^2*(1+2*(3*w)) by ring]
  exact Nat.ordCompl_pow_mul_of_not_dvd 2 Nat.prime_two (by omega)

private theorem contractionSteps (d u : ℕ) :
    ∀ i : ℕ, i < d →
      3*syracuseStep^[i] (1+2*(4^d*u))+1 =
        4*syracuseStep^[i+1] (1+2*(4^d*u)) := by
  induction d generalizing u with
  | zero => intro i hi; omega
  | succ d ih =>
    have es : syracuseStep (1+2*(4^(d+1)*u)) = 1+2*(4^d*(3*u)) := by
      rw [pow_succ' (4:ℕ), Nat.mul_assoc, twoHalvings]
      ring
    intro i hi
    cases i with
    | zero =>
      change 3*(1+2*(4^(d+1)*u))+1 = 4*syracuseStep (1+2*(4^(d+1)*u))
      rw [es, pow_succ (4:ℕ)]
      ring
    | succ i =>
      simp only [Function.iterate_succ_apply, es]
      exact ih (3*u) i (by omega)

theorem solution (y d : ℕ) (hy : 0 < y) (ho : ¬ 2 ∣ y) :
    (∀ i : ℕ, i < d →
      3*syracuseStep^[i] y+1 = 4*syracuseStep^[i+1] y) ↔
    2*4^d ∣ y-1 := by
  refine ⟨contractionStart d y hy ho, ?_⟩
  rintro ⟨u, hu⟩
  have e : y = 1+2*(4^d*u) := by rw [Nat.mul_assoc] at hu; omega
  rw [e]
  exact contractionSteps d u
