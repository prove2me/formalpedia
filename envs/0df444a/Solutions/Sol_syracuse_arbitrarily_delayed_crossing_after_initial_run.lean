-- Prove2me | solution 1 for syracuse_arbitrarily_delayed_crossing_after_initial_run
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T12:36:53.955516+00:00
-- url     : https://prove2.me/submissions/529a9c17-90bb-491c-b9a9-897b849c32fb

import Theorems.Thm_syracuse_exact_contraction_block
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

open Nat

private theorem inverseClass (a p : ℕ) (hp : 1 < p) (hac : a.Coprime p) :
    ∃ r < p, ∀ q : ℕ, a*q % p = 1 ↔ q % p = r := by
  let z := Nat.chineseRemainder hac 0 1
  obtain ⟨c,hc⟩ := Nat.modEq_zero_iff_dvd.mp z.property.1
  have inv : a*c ≡ 1 [MOD p] := hc ▸ z.property.2
  refine ⟨c%p, Nat.mod_lt _ (by omega), ?_⟩
  intro q
  have hone : 1 % p = 1 := Nat.mod_eq_of_lt hp
  constructor
  · intro h
    have hq : a*q ≡ 1 [MOD p] := Eq.trans h hone.symm
    exact Nat.ModEq.cancel_left_of_coprime hac.symm (hq.trans inv.symm)
  · intro h
    exact Eq.trans (((show q ≡ c [MOD p] from h).mul_left a).trans inv) hone

private theorem growthBounds (k : ℕ) (hk : 6 ≤ k) :
    3*2^k ≤ (3:ℕ)^k ∧ 2*8^k ≤ (9:ℕ)^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    obtain ⟨h1,h2⟩ := ih
    simp only [pow_succ]
    constructor <;> omega

private theorem compareEndpoints (a m d u q : ℕ)
    (ha : 0 < a) (hm : 0 < m) (hu : 0 < u) (hq : 0 < q)
    (hrel : a*q = 3+4*(d*d)*u) (hstart : 3*m ≤ a)
    (hmid : 2*m*d ≤ a*a) (hend : a*a*a ≤ m*d*d) :
    m*q-1 < 1+2*(a*(d*u)) ∧ 1+2*(a*a*u) < m*q-1 := by
  have mid : a*(m*q) ≤ a*(1+2*(a*(d*u))) := calc
    a*(m*q) = m*(a*q) := by ring
    _ = 3*m + (2*m*d)*(2*d*u) := by rw [hrel]; ring
    _ ≤ a + (a*a)*(2*d*u) := Nat.add_le_add hstart (Nat.mul_le_mul_right _ hmid)
    _ = _ := by ring
  have hmid' := Nat.le_of_mul_le_mul_left mid ha
  have hmq := Nat.mul_pos hm hq
  have h1 : a ≤ a*a*a := (Nat.le_mul_of_pos_right a ha).trans (Nat.le_mul_of_pos_right _ ha)
  have h2 := (h1.trans hend).trans (Nat.le_mul_of_pos_right _ hu)
  have h3 := Nat.mul_le_mul_right u hend
  have e : a*((1+2*(a*a*u))+1) < a*(m*q) := calc
    a*((1+2*(a*a*u))+1) = 2*a+2*((a*a*a)*u) := by ring
    _ ≤ 2*((m*d*d)*u)+2*((m*d*d)*u) := by omega
    _ < 3*m+4*((m*d*d)*u) := by omega
    _ = m*(a*q) := by rw [hrel]; ring
    _ = _ := by ring
  have small := Nat.lt_of_mul_lt_mul_left e
  exact ⟨by omega, by omega⟩

private theorem delay (k q : ℕ) (hk : 6 ≤ k) (hq : 0 < q)
    (hclass : (3^(k-1)*q) % 4^(2*k+1) = 1) :
    let n := 2^k*q-1
    let y := ordCompl[2] (3^k*q-1)
    (∀ j : ℕ, j ≤ k → n < syracuseStep^[j] y) ∧
    syracuseStep^[2*k] y < n ∧
    (∀ j : ℕ, j < 2*k → syracuseStep^[j+1] y < syracuseStep^[j] y) := by
  let p := 4^(2*k+1)
  have hp : 1 < p := Nat.one_lt_pow (by omega) (by decide)
  have hm : 3^(k-1)*q ≡ 1 [MOD p] := Eq.trans hclass (Nat.mod_eq_of_lt hp).symm
  have hpq : 0 < 3^(k-1)*q := Nat.mul_pos (pow_pos (by decide) _) hq
  obtain ⟨v,hv⟩ := (Nat.modEq_iff_dvd' hpq).mp hm.symm
  have hprod : 3^(k-1)*q = 1+p*v := by omega
  have big : 1 < (3:ℕ)^(k-1) := Nat.one_lt_pow (by omega) (by decide)
  have hlarge := Nat.le_mul_of_pos_right ((3:ℕ)^(k-1)) hq
  have hvpos : 0 < v := by
    by_contra! h
    have ev : v = 0 := by omega
    rw [ev, Nat.mul_zero, Nat.add_zero] at hprod
    omega
  let u := 3*v
  have hu : 0 < u := by dsimp [u]; omega
  have rel : 3^k*q = 3+4*(4^(2*k))*u := calc
    3^k*q = 3*(3^(k-1)*q) := by
      conv_lhs => rw [show k=(k-1)+1 by omega, pow_succ' (3:ℕ)]
      ring
    _ = _ := by rw [hprod]; dsimp [p,u]; rw [pow_succ (4:ℕ)]; ring
  let start := 1+2*(4^(2*k)*u)
  have he : 3^k*q-1 = 2^1*start  := by
    dsimp [start]
    rw [rel, Nat.mul_assoc]
    omega
  have ey : ordCompl[2] (3^k*q-1) = start := by
    rw [he]
    exact Nat.ordCompl_pow_mul_of_not_dvd 1 Nat.prime_two (by dsimp [start]; omega)
  dsimp only
  rw [ey]
  obtain ⟨val,fall⟩ := syracuse_exact_contraction_block (2*k) u hu
  change ∀ i : ℕ, i ≤ 2*k → syracuseStep^[i] start = _ at val
  change ∀ i : ℕ, i < 2*k → syracuseStep^[i+1] start < syracuseStep^[i] start at fall
  have offset : (4:ℕ)^(2*k)=4^k*4^k := by rw [two_mul, pow_add]
  have sq : (9:ℕ)^k=3^k*3^k := mul_pow 3 3 k
  have eight : (8:ℕ)^k=2^k*4^k := mul_pow 2 4 k
  have endScale : (3:ℕ)^k*3^k*3^k ≤ 2^k*4^k*4^k := by
    simpa only [mul_pow] using
      (Nat.pow_le_pow_left (by decide : (3:ℕ)*3*3 ≤ 2*4*4) k)
  obtain ⟨b1,b2⟩ := growthBounds k hk
  rw [sq,eight] at b2
  obtain ⟨mid,last⟩ := compareEndpoints (3^k) (2^k) (4^k) u q
    (pow_pos (by decide) _) (Nat.two_pow_pos _) hu hq (by rwa [offset] at rel)
    b1 (by simpa only [Nat.mul_assoc] using b2) endScale
  have middle : 2^k*q-1 < syracuseStep^[k] start := by
    rw [val k (by omega), show 2*k-k=k by omega]
    exact mid
  have late : syracuseStep^[2*k] start < 2^k*q-1 := by
    rw [val (2*k) le_rfl]
    simpa only [Nat.sub_self, pow_zero, one_mul, two_mul k, pow_add, Nat.mul_assoc] using last
  refine ⟨?_, late, fall⟩
  intro j hj
  have chain (i : ℕ) (hi : j ≤ i) (hi' : i ≤ 2*k) :
      syracuseStep^[i] start ≤ syracuseStep^[j] start := by
    induction i, hi using Nat.le_induction with
    | base => exact le_rfl
    | succ i _ ih => exact (fall i (by omega)).le.trans (ih (by omega))
  exact middle.trans_le (chain k hj (by omega))

theorem solution (k : ℕ) (hk : 6 ≤ k) :
    ∃ r < 4^(2*k+1),
      (∀ q : ℕ, (3^(k-1)*q) % 4^(2*k+1) = 1 ↔ q % 4^(2*k+1) = r) ∧
      ∀ q : ℕ, 0 < q → q % 4^(2*k+1) = r →
        let n := 2^k*q-1
        let y := ordCompl[2] (3^k*q-1)
        (∀ j : ℕ, j ≤ k → n < syracuseStep^[j] y) ∧
        syracuseStep^[2*k] y < n ∧
        (∀ j : ℕ, j < 2*k → syracuseStep^[j+1] y < syracuseStep^[j] y) := by
  have co : ((3:ℕ)^(k-1)).Coprime (4^(2*k+1)) := ((by decide : Nat.Coprime 3 4).pow_left _).pow_right _
  obtain ⟨r,hr,rule⟩ := inverseClass _ _ (Nat.one_lt_pow (by omega) (by decide)) co
  exact ⟨r,hr,rule,fun q hq h => delay k q hk hq ((rule q).mpr h)⟩
