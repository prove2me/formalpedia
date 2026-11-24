-- Prove2me | solution 1 for syracuse_initial_run_block_crossing_certificate
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T17:05:32.354715+00:00
-- url     : https://prove2.me/submissions/48fa51c2-c7ca-4917-b8da-bb44dc846d09

import Theorems.Thm_syracuse_contraction_length_iff_dvd
import Theorems.Thm_syracuse_exact_contraction_block
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

open Nat

private theorem liftContraction (A q s d y : ℕ)
    (hy : 0 < y) (ho : ¬ 2 ∣ y) (e : 2^s*y+1=A*q) :
    (∀ i : ℕ, i < d → 3*syracuseStep^[i] y+1 = 4*syracuseStep^[i+1] y) ↔
      A*q ≡ 1+2^s [MOD 2^(s+1)*4^d] := by
  have hprod : 2^(s+1)*4^d = 2^s*(2*4^d) := by rw [pow_succ, Nat.mul_assoc]
  have hdecomp : 2^s*y+1 = 1+2^s+2^s*(y-1) := by
    calc
      2^s*y+1 = 2^s*((y-1)+1)+1 := by rw [Nat.sub_add_cancel hy]
      _ = _ := by ring
  rw [syracuse_contraction_length_iff_dvd y d hy ho, ← e, hdecomp,
    Nat.add_modEq_left_iff, hprod, Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos s)]

private theorem decode (a q s d : ℕ) (hs : 0 < s)
    (hc : a*q ≡ 1+2^s [MOD 2^(s+1)*4^d]) :
    let p := 2^(s+1)*4^d
    let u := (a*q-(1+2^s))/p
    a*q=1+2^s+p*u := by
  dsimp only
  let p := 2^(s+1)*4^d
  have hpow : 2 ≤ (2:ℕ)^s := Nat.one_lt_pow (by omega) (by decide)
  have hp : 0 < p := Nat.mul_pos (Nat.two_pow_pos _) (pow_pos (by decide) _)
  have hz : 1+2^s < p := by
    apply lt_of_lt_of_le _ (Nat.le_mul_of_pos_right (2^(s+1)) (pow_pos (by decide : 0 < (4:ℕ)) d))
    rw [pow_succ (2:ℕ) s]
    omega
  have hle : 1+2^s ≤ a*q := by
    by_contra! h
    have eq := hc
    change (a*q)%p=(1+2^s)%p at eq
    rw [Nat.mod_eq_of_lt (h.trans hz), Nat.mod_eq_of_lt hz] at eq
    omega
  obtain ⟨u, hu⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hc.symm
  change a*q = 1+2^s+p*((a*q-(1+2^s))/p)
  nth_rw 2 [hu]
  rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hp]
  exact hu

theorem solution (k q s d : ℕ) (hs : 0 < s)
    (hgt : 1+2^s < 3^k*q) :
    let n := 2^k*q-1
    let y := ordCompl[2] (3^k*q-1)
    let p := 2^(s+1)*4^d
    let u := (3^k*q-(1+2^s))/p
    ((2^s*y = 3^k*q-1 ∧
      (∀ i : ℕ, i < d → 3*syracuseStep^[i] y+1 = 4*syracuseStep^[i+1] y)) ↔
        (3^k*q) % p = (1+2^s) % p) ∧
      ((3^k*q) % p = (1+2^s) % p →
        (∀ i : ℕ, i ≤ d → syracuseStep^[i] y = 1+2*(3^i*(4^(d-i)*u))) ∧
        (syracuseStep^[d] y < n ↔ 2+2*(3^d*u) < 2^k*q)) := by
  dsimp only
  let y := ordCompl[2] (3^k*q-1)
  let p := 2^(s+1)*4^d
  let u := (3^k*q-(1+2^s))/p
  have h1 : 1 < 3^k*q := (Nat.le_add_right 1 (2^s)).trans_lt hgt
  have hz : 3^k*q-1 ≠ 0 := (Nat.sub_pos_iff_lt.mpr h1).ne'
  have hy : 0 < y := Nat.ordCompl_pos 2 hz
  have ho : ¬ 2 ∣ y := Nat.not_dvd_ordCompl Nat.prime_two hz
  have fromResidue (hc : 3^k*q ≡ 1+2^s [MOD p]) :
      2^s*y=3^k*q-1 ∧ y=1+2*(4^d*u) ∧ 0<u := by
    have rel : 3^k*q = 1+2^s+p*u := decode _ _ _ _ hs hc
    have hu : 0 < u := by
      apply Nat.pos_of_ne_zero
      intro ez
      apply hgt.ne'
      simpa only [ez, Nat.mul_zero, Nat.add_zero] using rel
    have e : 3^k*q-1 = 2^s*(1+2*(4^d*u)) := by
      have eqn : 1+2^s+p*u = 2^s*(1+2*(4^d*u))+1 := by
        dsimp [p]
        rw [pow_succ (2:ℕ) s]
        ring
      rw [rel, eqn, Nat.add_sub_cancel]
    have en : y=1+2*(4^d*u) := by
      unfold y
      rw [e, Nat.ordCompl_pow_mul_of_not_dvd s Nat.prime_two (by omega)]
    exact ⟨by rw [en, e], en, hu⟩
  have fromVal (h : 2^s*y=3^k*q-1) : 2^s*y+1=3^k*q := by
    rw [h, Nat.sub_add_cancel h1.le]
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨h, steps⟩
      exact (liftContraction (3^k) q s d y hy ho (fromVal h)).mp steps
    · intro hc
      obtain ⟨h, _, _⟩ := fromResidue hc
      exact ⟨h, (liftContraction (3^k) q s d y hy ho (fromVal h)).mpr hc⟩
  · intro hc
    obtain ⟨_, en, hu⟩ := fromResidue hc
    have vals := (syracuse_exact_contraction_block d u hu).1
    have vf (i : ℕ) (hi : i ≤ d) :
        syracuseStep^[i] y = 1+2*(3^i*(4^(d-i)*u)) := by
      rw [en]
      exact vals i hi
    refine ⟨vf, ?_⟩
    change (syracuseStep^[d] y < 2^k*q-1) ↔ 2+2*(3^d*u) < 2^k*q
    rw [vf d le_rfl, Nat.sub_self, pow_zero, Nat.one_mul]
    omega
