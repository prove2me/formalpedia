-- Prove2me | solution 1 for syracuse_odd_nondescending_minimum_mod4096
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T11:22:57.188208+00:00
-- url     : https://prove2.me/submissions/04309e5c-35db-44cf-8bd5-62a4a75bac6b

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.NormNum

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/- Affine stepping and the odd-part simulation adapted from immiq's accepted
Prove2Me solution 15e9cc1c-1fe1-48ea-9827-5a349c909d76, Apache-2.0 via the
Prove2Me terms. The finite coefficient sieve is new to this proof. -/

private def halfStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

private def nextSlope (c t : ℕ) : ℕ :=
  if c % 2 = 0 then t else 3 * t

private theorem affineStep (c t k : ℕ) :
    halfStep (c + 2 * (t * k)) = halfStep c + nextSlope c t * k := by
  have hmod : (c + 2 * (t * k)) % 2 = c % 2 := by omega
  by_cases he : c % 2 = 0
  · simp [halfStep, nextSlope, hmod, he]
    omega
  · simp [halfStep, nextSlope, hmod, he, Nat.mul_assoc]
    omega


private def multiplier : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h+1, r => multiplier h (halfStep r) * nextSlope r 1

private theorem affineIter (h r k : ℕ) :
    halfStep^[h] (r+2^h*k) = halfStep^[h] r + multiplier h r*k := by
  induction h generalizing r k with
  | zero => simp [multiplier]
  | succ h ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pow_succ,
      show 2^h*2*k = 2*(1*(2^h*k)) by ring, affineStep,
      show nextSlope r 1 * (2^h*k) = 2^h*(nextSlope r 1*k) by ring, ih, multiplier]
    rw [Nat.mul_assoc]

private def oddPart (n : ℕ) : ℕ := ordCompl[2] n

private theorem oddPart_half (n : ℕ) :
    ∃ k : ℕ, syracuseStep^[k] (oddPart n) = oddPart (halfStep n) := by
  by_cases he : n % 2 = 0
  · refine ⟨0, ?_⟩
    simpa [oddPart, halfStep, he] using
      (Nat.ordCompl_div_of_dvd Nat.prime_two (Nat.dvd_of_mod_eq_zero he)).symm
  · have ho : oddPart n = n :=
      (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n Nat.prime_two).mpr (Or.inr (by omega))
    refine ⟨1, ?_⟩
    rw [ho, Function.iterate_one]
    simpa [syracuseStep, oddPart, halfStep, he] using
      (Nat.ordCompl_div_of_dvd Nat.prime_two (show 2 ∣ 3*n+1 by omega)).symm

private theorem liftHalf (n j : ℕ) :
    ∃ k : ℕ, syracuseStep^[k] (oddPart n) = oddPart (halfStep^[j] n) := by
  induction j with
  | zero => exact ⟨0,rfl⟩
  | succ j ih =>
    obtain ⟨k,hk⟩ := ih
    obtain ⟨l,hl⟩ := oddPart_half (halfStep^[j] n)
    exact ⟨l+k, by rw [Function.iterate_add_apply, hk, Function.iterate_succ_apply', hl]⟩


private theorem noDrops (n : ℕ) (hn : n%2=1)
    (hm : ∀ j : ℕ, n ≤ syracuseStep^[j] n) :
    ∀ j : ℕ, n ≤ halfStep^[j] n := by
  intro j
  obtain ⟨k,hk⟩ := liftHalf n j
  have hodd : oddPart n = n :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n Nat.prime_two).mpr (Or.inr (by omega))
  rw [hodd] at hk
  exact (hm k).trans (hk.trans_le (Nat.div_le_self _ _))

private abbrev sieveMask : ℕ := 0x8800800000000000800000808000000080008080080000008000000088000000880080800000800080000080880000008000808000000000000080008800000080008000800080008000000088000000800000800000008080008000080000008800808000008000800000808800000080008080080000008000000088000000880080008000000080000080000000008000808000000080800000008800000088008080000080008000008088000000800080800800000000008000000000008000808080008000800000008800000080000080000000808000000008000000880080808000800000000080800000008000808008000080800080008800000088000000800000008000008080000000800080800800008000000000080000008000808000008000800000008800000080000080080000000000800088000000800080808000800080000000800000008000008000000080800080000800000088008080800000008000008088000000800080800800008000008000880000008000800080000000800000008000000080000080080000808000000088000000880080800000800080000080880000008000800008000000000080008800000080008080800000008000000088000000000000800000008080008000080000008800800080008000800000808800000080008080080000808000800088000000

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem checkResidues : ∀ r : Fin 4096, (r.val%2=1) →
    sieveMask.testBit r.val = false →
    ∃ j : Fin 13, halfStep^[j.val] (1048576+r.val) < 1048576+r.val ∧
      multiplier j.val (1048576+r.val) ≤ 2^j.val := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem countResidues :
    ((Finset.range 4096).filter (fun r => sieveMask.testBit r = true)).card = 226 := by
  decide +kernel

theorem solution :
    ((Finset.range 4096).filter (fun r => (0x8800800000000000800000808000000080008080080000008000000088000000880080800000800080000080880000008000808000000000000080008800000080008000800080008000000088000000800000800000008080008000080000008800808000008000800000808800000080008080080000008000000088000000880080008000000080000080000000008000808000000080800000008800000088008080000080008000008088000000800080800800000000008000000000008000808080008000800000008800000080000080000000808000000008000000880080808000800000000080800000008000808008000080800080008800000088000000800000008000008080000000800080800800008000000000080000008000808000008000800000008800000080000080080000000000800088000000800080808000800080000000800000008000008000000080800080000800000088008080800000008000008088000000800080800800008000008000880000008000800080000000800000008000000080000080080000808000000088000000880080800000800080000080880000008000800008000000000080008800000080008080800000008000000088000000000000800000008080008000080000008800800080008000800000808800000080008080080000808000800088000000 : ℕ).testBit r = true)).card = 226 ∧
    ∀ x : ℕ, 1048576 ≤ x → x%2=1 → (∀ j : ℕ, x ≤ syracuseStep^[j] x) →
      (0x8800800000000000800000808000000080008080080000008000000088000000880080800000800080000080880000008000808000000000000080008800000080008000800080008000000088000000800000800000008080008000080000008800808000008000800000808800000080008080080000008000000088000000880080008000000080000080000000008000808000000080800000008800000088008080000080008000008088000000800080800800000000008000000000008000808080008000800000008800000080000080000000808000000008000000880080808000800000000080800000008000808008000080800080008800000088000000800000008000008080000000800080800800008000000000080000008000808000008000800000008800000080000080080000000000800088000000800080808000800080000000800000008000008000000080800080000800000088008080800000008000008088000000800080800800008000008000880000008000800080000000800000008000000080000080080000808000000088000000880080800000800080000080880000008000800008000000000080008800000080008080800000008000000088000000000000800000008080008000080000008800800080008000800000808800000080008080080000808000800088000000 : ℕ).testBit (x%4096) = true := by
  refine ⟨countResidues,?_⟩
  intro x hx ho hm
  let r : Fin 4096 := ⟨x%4096, Nat.mod_lt _ (by decide)⟩
  change sieveMask.testBit r.val = true
  cases hBit : sieveMask.testBit r.val with
  | true => rfl
  | false =>
    have hr : r.val%2=1 := by dsimp [r]; omega
    obtain ⟨j,hlt,hcoef⟩ := checkResidues r hr hBit
    let q := x/4096 - (1048576/4096)
    have hrEq : x = (1048576+r.val)+2^12*q := by dsimp [r,q]; omega
    have hj : j.val ≤ 12 := by have := j.isLt; omega
    have hindex : j.val+(12-j.val)=12 := by omega
    have hpow : 2^12=2^j.val*2^(12-j.val) := by rw [← pow_add,hindex]
    have hcoef' : multiplier j.val (1048576+r.val)*2^(12-j.val) ≤ 2^12 := by
      rw [hpow]
      exact Nat.mul_le_mul_right _ hcoef
    have hval : halfStep^[j.val] x =
        halfStep^[j.val] (1048576+r.val) + (multiplier j.val (1048576+r.val)*2^(12-j.val))*q := by
      conv_lhs => rw [hrEq,hpow, Nat.mul_assoc,affineIter,← Nat.mul_assoc]
    have hlast := Nat.mul_le_mul_right q hcoef'
    have hbad : halfStep^[j.val] x < x := by omega
    exact False.elim ((not_lt_of_ge (noDrops x ho hm j.val)) hbad)
