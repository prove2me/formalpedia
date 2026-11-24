-- Prove2me | solution 1 for syracuse_initial_run_endpoint_and_growth
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T11:40:31.615128+00:00
-- url     : https://prove2.me/submissions/5185e00e-e090-42ae-9129-d3895831e5eb

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

open Nat

private theorem runEnd (u : ℕ) (hu : 0 < u) :
    syracuseStep (2*u-1) = ordCompl[2] (3*u-1) := by
  have e : 3*(2*u-1)+1 = 2^1*(3*u-1) := by omega
  exact (congrArg (fun z : ℕ => ordCompl[2] z) e).trans
    (Nat.ordCompl_self_pow_mul _ 1 Nat.prime_two)

private theorem climb (u : ℕ) (hu : 0 < u) :
    syracuseStep (2*(2*u)-1) = 2*(3*u)-1 := by
  rw [runEnd _ (by omega)]
  have hodd : ¬2 ∣ 3*(2*u)-1 := by omega
  rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr (Or.inr hodd)]
  omega

private theorem runPrefix (j u : ℕ) (hu : 0 < u) :
    syracuseStep^[j] (2^j*(2*u)-1) = 3^j*(2*u)-1 := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, pow_succ' (2:ℕ),
      show 2*2^j*(2*u) = 2*(2*(2^j*u)) by ring,
      climb _ (Nat.mul_pos (Nat.two_pow_pos j) hu),
      show 2*(3*(2^j*u)) = 2^j*(2*(3*u)) by ring, ih _ (by omega),
      pow_succ (3:ℕ)]
    ring_nf

/-- The step that closes the initial run, and strict growth above the start
    at every earlier positive index. The cofactor need only be positive. -/
theorem solution (k q : ℕ) (hk : 0 < k) (hq : 0 < q) :
    syracuseStep^[k] (2^k*q-1) = ordCompl[2] (3^k*q-1) ∧
    ∀ j : ℕ, 0 < j → j < k →
      2^k*q-1 < syracuseStep^[j] (2^k*q-1) := by
  constructor
  · obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Function.iterate_succ_apply', pow_succ (2:ℕ), Nat.mul_assoc, runPrefix l q hq,
      show 3^l*(2*q) = 2*(3^l*q) by ring,
      runEnd _ (Nat.mul_pos (pow_pos (by decide : 0 < (3:ℕ)) l) hq), pow_succ' (3:ℕ), Nat.mul_assoc]
  · intro j hj hjk
    let u := 2^(k-(j+1))*q
    have hu : 0 < u := Nat.mul_pos (Nat.two_pow_pos _) hq
    have e : 2^k*q = 2^j*(2*u) := by
      calc
        2^k*q = 2^(j+(1+(k-(j+1))))*q := by congr 2; omega
        _ = 2^j*(2*u) := by simp only [pow_add, pow_one, u]; ring
    rw [e, runPrefix j u hu]
    have hp : (2:ℕ)^j < 3^j := Nat.pow_lt_pow_left (by decide) (by omega)
    have hh := Nat.mul_lt_mul_of_pos_right hp (by omega : 0 < 2*u)
    have hl := Nat.mul_pos (Nat.two_pow_pos j) (by omega : 0 < 2*u)
    omega
