-- Prove2me | solution 1 for syracuse_descent_twentyseven_mod32_mod2097152_step18_mod536870912_chunk12
-- status  : ACCEPTED   (prove)
-- author  : @Siyuan Chen
-- created : 2026-11-23T17:10:29.374608+00:00
-- url     : https://prove2.me/submissions/7e6fd3b1-0a8c-4c0a-8710-1d299f9797ce

import Definitions.Def_syracuseStep
import Definitions.Def_syrStep18Chunk12
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Theorems.Thm_CollatzFrontier_syracuse_terminal_budget_of_descent

set_option maxRecDepth 16384
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Uniform 17-row Syracuse descent on one chunk of residue classes modulo `2 ^ 29`

Same certificate architecture as the modulus-`2 ^ 21`, `2 ^ 23` and `2 ^ 24` theorems of this branch:
the checker `chk 17 r 29 r` replays 17 exact rows `3 b_i + 1 = 2 ^ a_i * b_(i+1)` and closes
with a truncated terminal row `3 b_16 + 1 = 2 ^ e * B`, `e = min a_16 (27 - S_16)`, `B < r`;
`chk_sound` feeds the hypothesis package of `CollatzFrontier.syracuse_terminal_budget_of_descent`
(budget `S_16 + e ≤ 27`), and one kernel evaluation checks the literal chunk.
-/

namespace SyrDescTwentysevenMod536870912Chunk12

/-- Fuel-bounded 2-adic valuation; for any fuel `2 ^ (v2 f x)` divides `x` (`two_pow_v2_dvd`). -/
def v2 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, x => if x % 2 = 0 then v2 f (x / 2) + 1 else 0

/-- Exponent proposed for the row leaving `x`. -/
def ev (x : ℕ) : ℕ := v2 32 (3 * x + 1)

/-- Quotient of the row leaving `x`; `3 * x + 1 = 2 ^ ev x * nxt x` always (`row_eq`). -/
def nxt (x : ℕ) : ℕ := (3 * x + 1) / 2 ^ ev x

/-- `chk k x rem r`: `k` exact rows starting at `x` with odd quotients and exponent sum at most
`rem`, then a terminal row whose exponent is truncated to the remaining budget and whose
quotient is below `r`. -/
def chk : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, x, rem, r => decide ((3 * x + 1) / 2 ^ min (ev x) rem < r)
  | k + 1, x, rem, r =>
      decide (ev x ≤ rem) && (decide (nxt x % 2 = 1) && chk k (nxt x) (rem - ev x) r)

/-- The proposed exponent is always a genuine divisor exponent. -/
theorem two_pow_v2_dvd : ∀ (f x : ℕ), 2 ^ v2 f x ∣ x := by
  intro f
  induction f with
  | zero => intro x; simp [v2]
  | succ f ih =>
    intro x
    unfold v2
    split_ifs with hx
    · obtain ⟨c, hc⟩ := ih (x / 2)
      refine ⟨c, ?_⟩
      have h2 : x = 2 * (x / 2) := by omega
      calc x = 2 * (x / 2) := h2
        _ = 2 * (2 ^ v2 f (x / 2) * c) := by rw [← hc]
        _ = 2 ^ (v2 f (x / 2) + 1) * c := by ring
    · simp

/-- Every row is an exact factorisation. -/
theorem row_eq (x : ℕ) : 3 * x + 1 = 2 ^ ev x * nxt x :=
  (Nat.mul_div_cancel' (two_pow_v2_dvd 32 (3 * x + 1))).symm

/-- An accepting run produces odd intermediate quotients and a terminal divisor row within the
budget, in the form consumed by `CollatzFrontier.syracuse_terminal_budget_of_descent`. -/
theorem chk_sound : ∀ (k x rem r : ℕ), chk k x rem r = true →
    (∀ i < k, nxt^[i + 1] x % 2 = 1) ∧
    ∃ e B : ℕ, 3 * nxt^[k] x + 1 = 2 ^ e * B ∧
      (∑ i ∈ Finset.range k, ev (nxt^[i] x)) + e ≤ rem ∧ B < r := by
  intro k
  induction k with
  | zero =>
    intro x rem r h
    simp only [chk, decide_eq_true_eq] at h
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), min (ev x) rem,
      (3 * x + 1) / 2 ^ min (ev x) rem, ?_, ?_, h⟩
    · have hd : 2 ^ min (ev x) rem ∣ 3 * x + 1 :=
        Dvd.dvd.trans (pow_dvd_pow 2 (Nat.min_le_left _ _)) (two_pow_v2_dvd 32 (3 * x + 1))
      simpa using (Nat.mul_div_cancel' hd).symm
    · simp
  | succ k ih =>
    intro x rem r h
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hle, hodd, hrest⟩ := h
    obtain ⟨hodds, e, B, hfin, hbud, hdesc⟩ := ih (nxt x) (rem - ev x) r hrest
    refine ⟨?_, e, B, ?_, ?_, hdesc⟩
    · intro i hi
      cases i with
      | zero => simpa using hodd
      | succ i =>
        rw [Function.iterate_succ_apply]
        exact hodds i (by omega)
    · rw [Function.iterate_succ_apply]; exact hfin
    · rw [Finset.sum_range_succ']
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
      omega

/-- One accepted residue gives descent on its whole class, by the published terminal-budget
theorem. -/
theorem class_descent (r : ℕ) (hc : chk 17 r 29 r = true) (q : ℕ) :
    syracuseStep^[18] (r + 2 ^ 29 * q) < r + 2 ^ 29 * q := by
  obtain ⟨hodds, e, B, hfin, hbud, hdesc⟩ := chk_sound 17 r 29 r hc
  exact CollatzFrontier.syracuse_terminal_budget_of_descent
    (fun i => ev (nxt^[i] r)) (fun i => nxt^[i] r) r 29 17 e B rfl
    (fun i _ => by
      show 3 * nxt^[i] r + 1 = 2 ^ ev (nxt^[i] r) * nxt^[i + 1] r
      rw [Function.iterate_succ_apply']
      exact row_eq _)
    (fun i hi => Nat.odd_iff.mpr (hodds i hi)) hfin hbud hdesc q

/-- The kernel evaluates the checker on every residue of the chunk. -/
theorem all_checked : ∀ r ∈ syrStep18Chunk12, chk 17 r 29 r = true := by
  decide +kernel

end SyrDescTwentysevenMod536870912Chunk12

theorem solution (n : ℕ)
    (h : n % 536870912 ∈ syrStep18Chunk12) :
    syracuseStep^[18] n < n := by
  have hc := SyrDescTwentysevenMod536870912Chunk12.all_checked _ h
  have hn : n = n % 536870912 + 2 ^ 29 * (n / 536870912) := by
    have := Nat.mod_add_div n 536870912
    omega
  rw [hn]
  exact SyrDescTwentysevenMod536870912Chunk12.class_descent _ hc _
