-- Prove2me | solution 1 for syracuse_primitive_word_affine_nondivisibility_ge_7621_with_rotated_baseline_2887463
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-20T10:42:54.380645+00:00
-- url     : https://prove2.me/submissions/0faf919e-05b6-43ac-b41c-d2a425f5ddd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_syracuse_primitive_word_affine_nondivisibility_sparse_8286
import Theorems.Thm_syracuse_word_baseline_budget_of_rotated_baseline

set_option autoImplicit false
set_option exponentiation.threshold 20000

-- Repeated-squaring certificate method adapted from the accepted Prove2Me
-- submission for syracuse_power_gap_baseline_budget_period_sparse_6291.
private def fastPow (a n : ℕ) : ℕ → ℕ
  | 0 => 1
  | fuel + 1 =>
      let x := fastPow a (n / 2) fuel
      if n % 2 = 0 then x * x else x * x * a

private theorem fastPow_eq (a n fuel : ℕ) (hn : n < 2 ^ fuel) :
    fastPow a n fuel = a ^ n := by
  induction fuel generalizing n with
  | zero =>
      have hz : n = 0 := by simpa using hn
      subst n
      rfl
  | succ fuel ih =>
      have hh : n / 2 < 2 ^ fuel := by
        rw [pow_succ] at hn
        omega
      simp only [fastPow, ih (n / 2) hh]
      split
      · have he : n = n / 2 + n / 2 := by omega
        rw [← pow_add, ← he]
      · have ho : n = n / 2 + n / 2 + 1 := by omega
        rw [← pow_add, ← pow_succ, ← ho]

private theorem blockMargin :
    (8662390 : ℕ) ^ 4296 < 2 ^ 6809 * 2887463 ^ 4296 := by
  have h : fastPow 8662390 4296 13 <
      fastPow 2 6809 13 * fastPow 2887463 4296 13 := by decide +kernel
  simpa only [fastPow_eq 8662390 4296 13 (by decide),
    fastPow_eq 2 6809 13 (by decide), fastPow_eq 2887463 4296 13 (by decide)] using h

private theorem sparseLengths (p K : ℕ) (hp : 7621 ≤ p)
    (hg : 3 ^ p < 2 ^ K)
    (hb : 2 ^ K * 2887463 ^ p ≤ 8662390 ^ p) :
    (p = 7621 ∧ K = 12079) ∨ 8286 ≤ p := by
  have hp0 : p ≠ 0 := by omega
  have hblock : (2 : ℕ) ^ 1054 < 3 ^ 665 := by decide +kernel
  have hlo : 1054 * p < 665 * K := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    calc
      (2 : ℕ) ^ (1054 * p) = (2 ^ 1054) ^ p := Nat.pow_mul 2 1054 p
      _ < (3 ^ 665) ^ p := Nat.pow_lt_pow_left hblock hp0
      _ = (3 ^ p) ^ 665 := Nat.pow_right_comm 3 665 p
      _ < (2 ^ K) ^ 665 := Nat.pow_lt_pow_left hg (by decide)
      _ = 2 ^ (665 * K) := (Nat.pow_mul' 2 665 K).symm
  have hhi : 4296 * K < 6809 * p := by
    have hb' : (2 : ℕ) ^ (4296 * K) * 2887463 ^ (4296 * p) ≤
        8662390 ^ (4296 * p) := by
      simpa only [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm K 4296,
        Nat.mul_comm p 4296] using Nat.pow_le_pow_left hb 4296
    have hm : (8662390 : ℕ) ^ (4296 * p) <
        2 ^ (6809 * p) * 2887463 ^ (4296 * p) := by
      simpa only [Nat.mul_pow, ← Nat.pow_mul] using Nat.pow_lt_pow_left blockMargin hp0
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
      (Nat.lt_of_mul_lt_mul_right (hb'.trans_lt hm))
  by_cases hlarge : 8286 ≤ p
  · exact Or.inr hlarge
  · let d := 665 * K - 1054 * p
    let t := 6809 * p - 4296 * K
    have hd : 0 < d := by dsimp [d]; omega
    have ht : 0 < t := by dsimp [t]; omega
    have hdEq : 665 * K = 1054 * p + d := by dsimp [d]; omega
    have htEq : 6809 * p = 4296 * K + t := by dsimp [t]; omega
    have hpEq : p = 665 * t + 4296 * d := by omega
    have hdOne : d = 1 := by omega
    have htFive : t = 5 := by omega
    exact Or.inl ⟨by omega, by omega⟩

theorem solution (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 7621 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2887463 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  have hbudget := syracuse_word_baseline_budget_of_rotated_baseline w 2887463 hgap
    hrotatedBaseline
  have hsparse := sparseLengths w.length w.sum hlength hgap hbudget
  exact syracuse_primitive_word_affine_nondivisibility_sparse_8286 w hpositive hlength hprimitive hgap hlow hlowSharp
    hbaselineBudget hrotatedBaseline hsparse
