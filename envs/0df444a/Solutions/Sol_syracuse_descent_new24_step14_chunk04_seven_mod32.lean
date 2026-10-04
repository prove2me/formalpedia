-- Prove2me | solution 1 for syracuse_descent_new24_step14_chunk04_seven_mod32
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T07:48:08.72063+00:00
-- url     : https://prove2.me/submissions/0a26bcc1-e93f-4b63-bf2d-23cd0caeeae0

import Mathlib
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseSevenMod32New24Step14Chunk04Classes
import Mathlib.Logic.Function.Iterate
set_option autoImplicit false
set_option maxRecDepth 200000

namespace SyrDescF70a410a

/-- Fuel-bounded 2-adic valuation (only used to propose an exponent; soundness re-checks it). -/
def v2 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, x => if x % 2 = 0 then v2 f (x / 2) + 1 else 0

/-- Run `s` Syracuse steps symbolically on the class `r + 2^k * m`. -/
def run : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, r, k => some (r, k)
  | s + 1, r, k =>
    if 2 ^ v2 64 (3 * r + 1) * ((3 * r + 1) / 2 ^ v2 64 (3 * r + 1)) = 3 * r + 1 ∧
        ((3 * r + 1) / 2 ^ v2 64 (3 * r + 1)) % 2 = 1 ∧ v2 64 (3 * r + 1) < k then
      run s ((3 * r + 1) / 2 ^ v2 64 (3 * r + 1)) (k - v2 64 (3 * r + 1))
    else none

/-- Certificate check for one residue. -/
def cert (r : ℕ) : Bool :=
  match run 14 r 24 with
  | some (r', k') => decide (r' < r ∧ 2 ^ k' * 3 ^ 14 ≤ 2 ^ 24)
  | none => false

theorem step_lemma (r r' a b m : ℕ) (hb : 1 ≤ b) (h : 2 ^ a * r' = 3 * r + 1)
    (hodd : r' % 2 = 1) :
    syracuseStep (r + 2 ^ (a + b) * m) = r' + 2 ^ b * (3 * m) := by
  unfold syracuseStep
  have hkey : 3 * (r + 2 ^ (a + b) * m) + 1 = 2 ^ a * (r' + 2 ^ b * (3 * m)) := by
    rw [pow_add]
    have : 3 * (r + 2 ^ a * 2 ^ b * m) + 1 = (3 * r + 1) + 2 ^ a * (2 ^ b * (3 * m)) := by ring
    rw [this, ← h]; ring
  rw [hkey]
  apply Nat.ordCompl_pow_mul_of_not_dvd a Nat.prime_two
  intro hd
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have he : r' + 2 ^ (c + 1) * (3 * m) = r' + 2 * (2 ^ c * (3 * m)) := by ring
  rw [he] at hd
  omega

theorem run_sound : ∀ (s r k r' k' : ℕ), run s r k = some (r', k') →
    ∀ m, syracuseStep^[s] (r + 2 ^ k * m) = r' + 2 ^ k' * (3 ^ s * m) := by
  intro s
  induction s with
  | zero =>
    intro r k r' k' h m
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ s ih =>
    intro r k r' k' h m
    simp only [run] at h
    split_ifs at h with hc
    obtain ⟨h1, h2, h3⟩ := hc
    rw [Function.iterate_succ_apply]
    have hk : k = v2 64 (3 * r + 1) + (k - v2 64 (3 * r + 1)) := by omega
    rw [hk, step_lemma r _ _ _ m (by omega) h1 h2, ih _ _ r' k' h (3 * m)]
    ring

theorem cert_sound (r : ℕ) (hc : cert r = true) (m : ℕ) :
    syracuseStep^[14] (r + 2 ^ 24 * m) < r + 2 ^ 24 * m := by
  unfold cert at hc
  split at hc
  · rename_i r' k' hrun
    rw [run_sound 14 r 24 r' k' hrun m]
    simp only [decide_eq_true_eq] at hc
    obtain ⟨h1, h2⟩ := hc
    have : 2 ^ k' * (3 ^ 14 * m) ≤ 2 ^ 24 * m := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right m h2
    omega
  · exact absurd hc (by simp)

theorem all_cert : ∀ r ∈ syracuseSevenMod32New24Step14Chunk04Classes, cert r = true := by
  decide +kernel

end SyrDescF70a410a

theorem solution (n : ℕ)
    (h : n % 16777216 ∈ syracuseSevenMod32New24Step14Chunk04Classes) :
    syracuseStep^[14] n < n := by
  have hc := SyrDescF70a410a.all_cert _ h
  have hn : n = n % 16777216 + 2 ^ 24 * (n / 16777216) := by
    have := Nat.mod_add_div n 16777216
    norm_num
    omega
  rw [hn]
  exact SyrDescF70a410a.cert_sound _ hc _
