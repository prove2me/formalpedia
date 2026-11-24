-- Prove2me | solution 1 for syracuse_first_descent_at_every_prescribed_time_mod_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T11:40:32.574003+00:00
-- url     : https://prove2.me/submissions/57a535da-92de-4107-83bc-5b3b89c93446

import Theorems.Thm_syracuse_initial_run_endpoint_and_growth
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

open Nat

private theorem room (k : ℕ) (hk : 2 ≤ k) : 3^k + 2^k ≤ (4:ℕ)^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    rw [pow_succ, pow_succ, pow_succ]
    omega

private theorem drop (k q : ℕ) (hk : 2 ≤ k) (hq : 0 < q)
    (hd : 2^k ∣ 3^k*q-1) : ordCompl[2] (3^k*q-1) < 2^k*q-1 := by
  obtain ⟨v, hv⟩ := hd
  rw [hv, Nat.ordCompl_self_pow_mul _ _ Nat.prime_two]
  apply lt_of_le_of_lt (Nat.ordCompl_le v 2)
  let m := 2^k
  have hm : 0 < m := Nat.two_pow_pos _
  have hn : 0 < m*q := Nat.mul_pos hm hq
  have hmle : m ≤ m*q := Nat.le_mul_of_pos_right _ hq
  have hroom := Nat.mul_le_mul_right q (room k hk)
  rw [Nat.add_mul, show (4:ℕ)^k = m*m from mul_pow 2 2 k, Nat.mul_assoc] at hroom
  change 3^k*q + m*q ≤ m*(m*q) at hroom
  have he : m*(m*q-1)+m = m*(m*q) := by
    rw [← Nat.mul_succ, show (m*q-1).succ = m*q by omega]
  have hpos : 0 < 3^k*q := Nat.mul_pos (pow_pos (by decide : 0 < (3:ℕ)) k) hq
  change 3^k*q-1 = m*v at hv
  exact Nat.lt_of_mul_lt_mul_left (show m*v < m*(m*q-1) by omega)

-- The congruence is solved once per k. Every lift of q0 modulo 2^k works.
theorem solution (k : ℕ) (hk : 4 ≤ k) :
    ∃ r : ℕ, r < 2^(2*k) ∧ ∀ b : ℕ,
      let n := r + 2^(2*k)*b
      n % 16 = 15 ∧ syracuseStep^[k] n < n ∧
        ∀ j : ℕ, 0 < j → j < k → n < syracuseStep^[j] n := by
  let m := 2^k
  let a := 3^k
  have hm : 1 < m := Nat.one_lt_pow (by omega) (by decide)
  have ha : 0 < a := pow_pos (by decide) _
  have co : a.Coprime m := ((by decide : Nat.Coprime 3 2).pow_left k).pow_right k
  let z := Nat.chineseRemainder co 0 1
  obtain ⟨q0, eq0⟩ := Nat.modEq_zero_iff_dvd.mp z.property.1
  have iz : z.val ≡ 1 [MOD m] := z.property.2
  have hz : z.val % m = 1 := Eq.trans iz (Nat.mod_eq_of_lt hm)
  have hq0 : 0 < q0 := by
    by_contra! h
    have : q0 = 0 := by omega
    simp [eq0, this] at hz
  have hq0lt : q0 < m := by
    have hlt := Nat.chineseRemainder_lt_mul co 0 1 ha.ne' (by omega)
    exact Nat.lt_of_mul_lt_mul_left (show a*q0 < a*m by rwa [← eq0])
  have es : 2^(2*k) = m*m := by rw [two_mul, pow_add]
  have hex : 0 < m*q0 := Nat.mul_pos (by omega) hq0
  refine ⟨m*q0-1, ?_, ?_⟩
  · rw [es]
    have := Nat.mul_lt_mul_of_pos_left hq0lt (by omega : 0 < m)
    omega
  intro b
  dsimp only
  let q := q0 + m*b
  have hq : 0 < q := by dsimp [q]; omega
  have hn : m*q0-1 + 2^(2*k)*b = 2^k*q-1 := by
    rw [es]
    change m*q0-1 + m*m*b = m*(q0+m*b)-1
    rw [Nat.mul_add, Nat.mul_assoc]
    omega
  have he : a*q = z.val+m*(a*b) := by dsimp [q]; rw [eq0]; ring
  have hv : a*q ≡ 1 [MOD m] := by
    change (a*q)%m = 1%m
    rw [he, Nat.add_mul_mod_self_left]
    exact iz
  have hdn : m ∣ a*q-1 := (Nat.modEq_iff_dvd' (Nat.mul_pos ha hq)).mp hv.symm
  rw [hn]
  obtain ⟨terminal, before⟩ := syracuse_initial_run_endpoint_and_growth k q (by omega) hq
  refine ⟨?_, terminal ▸ drop k q (by omega) hq hdn, before⟩
  have hd16 : 16 ∣ 2^k*q := dvd_mul_of_dvd_left (pow_dvd_pow 2 hk) q
  obtain ⟨t, ht⟩ := hd16
  have hp : 0 < 2^k*q := Nat.mul_pos (Nat.two_pow_pos k) hq
  omega
